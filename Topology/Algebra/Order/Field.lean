/-
Copyright (c) 2022 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Devon Tuma, Eric Rodriguez, Oliver Nash
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Order.Group

/-!
# Topologies on linear ordered fields

In this file we prove that a linear ordered field with order topology has continuous multiplication
and division (apart from zero in the denominator). We also prove theorems like
`Filter.Tendsto.mul_atTop`: if `f` tends to a positive number and `g` tends to positive infinity,
then `f * g` tends to positive infinity.
-/

public section


open Set Filter TopologicalSpace Function
open scoped Pointwise Topology
open OrderDual (toDual ofDual)

section Semifield

variable {𝕜 α : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α → 𝕜}

/-- In a linearly ordered semifield with the order topology, if `f` tends to `Filter.atTop` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atTop`. -/
/-
**Filter.Tendsto.atTop_mul_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atTop)
 (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop
参数：hC : 0 < C；hf : Tendsto f l atTop；hg : Tendsto g l (𝓝 C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.Tendsto.atTop_mul_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2

--- 原说明 ---
In a linearly ordered semifield with the order topology, if `f` tends to `Filter
.atTop` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atTop`.
-/
theorem Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ (hf.atTop_mul_const (half_pos hC))
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)), hf.eventually_ge_atTop 0] with x hg
    hf using mul_le_mul_of_nonneg_left hg.le hf

-- TODO: after removing this deprecated alias,
-- rename `Filter.Tendsto.atTop_mul'` to `Filter.Tendsto.atTop_mul`.
-- Same for the other 3 similar aliases below.
/-- In a linearly ordered semifield with the order topology, if `f` tends to a positive constant `C`
and `g` tends to `Filter.atTop` then `f * g` tends to `Filter.atTop`. -/
/-
**Filter.Tendsto.pos_mul_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.pos_mul_atTop {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
 (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop
参数：hC : 0 < C；hf : Tendsto f l (𝓝 C)；hg : Tendsto g l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.Tendsto.atTop_mul_pos`：Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atTop

--- 原说明 ---
In a linearly ordered semifield with the order topology, if `f` tends to a posit
ive constant `C`
and `g` tends to `Filter.atTop` then `f * g` tends to `Filter.atTop`.
-/
theorem Filter.Tendsto.pos_mul_atTop {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atTop_mul_pos hC hf

@[simp]
/-
**inv_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_atTop₀ : (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0 :=
  (((atTop_basis_Ioi' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis <|
    (nhdsGT_basis _).congr (by simp) fun a ha ↦ by simp [inv_Ioi₀ (inv_pos.2 ha)]

@[simp]
/-
**inv_nhdsGT_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_nhdsGT_zero : (𝓝[>] (0 : 𝕜))⁻¹ = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_atTop₀`：inv_atTop₀ : (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma inv_nhdsGT_zero : (𝓝[>] (0 : 𝕜))⁻¹ = atTop := by rw [← inv_atTop₀, inv_inv]

/-- The function `x ↦ x⁻¹` tends to `+∞` on the right of `0`. -/
/-
**tendsto_inv_nhdsGT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[>] (0 : 𝕜)) atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `inv_nhdsGT_zero`：inv_nhdsGT_zero : (𝓝[>] (0 : 𝕜))⁻¹ = atTop

--- 原说明 ---
The function `x ↦ x⁻¹` tends to `+∞` on the right of `0`.
-/
theorem tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[>] (0 : 𝕜)) atTop :=
  inv_nhdsGT_zero.le

/-- The function `r ↦ r⁻¹` tends to `0` on the right as `r → +∞`. -/
/-
**tendsto_inv_atTop_nhdsGT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_atTop_nhdsGT_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝[>] (0 
: 𝕜))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `inv_atTop₀`：inv_atTop₀ : (atTop : Filter 𝕜)⁻¹ = 𝓝[>] 0

--- 原说明 ---
The function `r ↦ r⁻¹` tends to `0` on the right as `r → +∞`.
-/
theorem tendsto_inv_atTop_nhdsGT_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝[>] (0 : 𝕜)) :=
  inv_atTop₀.le
/-
**tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop {f : 𝕜 -> α} (h : Tendsto (f
un x => f x⁻¹) atTop l) : Tendsto f (𝓝[>] 0) l
参数：h : Tendsto (fun x => f x⁻¹) atTop l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_nhdsGT_zero`：tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 =>
 x⁻¹) (𝓝[>] (0 : 𝕜)) atTop
-/
theorem tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop {f : 𝕜 → α}
    (h : Tendsto (fun x ↦ f x⁻¹) atTop l) :
    Tendsto f (𝓝[>] 0) l := by
  convert! h.comp tendsto_inv_nhdsGT_zero
  grind [inv_inv]
/-
**tendsto_inv_atTop_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `tendsto_inv_atTop_nhdsGT_zero`：tendsto_inv_atTop_nhdsGT_zero : Tendsto (
fun r : 𝕜 => r⁻¹) atTop (𝓝[>] (0 : 𝕜))
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_nhdsGT_zero.mono_right inf_le_left
/-
**Filter.Tendsto.inv_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.inv_tendsto_atTop (h : Tendsto f l atTop) : Tendsto f⁻¹ l (
𝓝 0)
参数：h : Tendsto f l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
-/
theorem Filter.Tendsto.inv_tendsto_atTop (h : Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0) :=
  tendsto_inv_atTop_zero.comp h
/-
**Filter.Tendsto.inv_tendsto_nhdsGT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.inv_tendsto_nhdsGT_zero (h : Tendsto f l (𝓝[>] 0)) : Tendst
o f⁻¹ l atTop
参数：h : Tendsto f l (𝓝[>] 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_nhdsGT_zero`：tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 =>
 x⁻¹) (𝓝[>] (0 : 𝕜)) atTop
-/
theorem Filter.Tendsto.inv_tendsto_nhdsGT_zero (h : Tendsto f l (𝓝[>] 0)) : Tendsto f⁻¹ l atTop :=
  tendsto_inv_nhdsGT_zero.comp h

/-- The function `x^(-n)` tends to `0` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_neg_atTop`. -/
/-
**tendsto_pow_neg_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_neg_atTop {n : Nat} (hn : n != 0) : Tendsto (fun x : 𝕜 => x ^ 
(-(n : Int))) atTop (𝓝 0)
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `Filter.tendsto_pow_atTop`：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Te
ndsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
The function `x^(-n)` tends to `0` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_neg_atTop`.
-/
theorem tendsto_pow_neg_atTop {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : 𝕜 => x ^ (-(n : ℤ))) atTop (𝓝 0) := by
  simpa only [zpow_neg, zpow_natCast] using! (tendsto_pow_atTop (α := 𝕜) hn).inv_tendsto_atTop
/-
**tendsto_zpow_atTop_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_zpow_atTop_zero {n : Int} (hn : n < 0) : Tendsto (fun x : 𝕜 => x ^
 n) atTop (𝓝 0)
参数：hn : n < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `tendsto_pow_neg_atTop`：tendsto_pow_neg_atTop {n : Nat} (hn : n != 0) : T
endsto (fun x : 𝕜 => x ^ (-(n : Int))) atTop (𝓝 0)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem tendsto_zpow_atTop_zero {n : ℤ} (hn : n < 0) :
    Tendsto (fun x : 𝕜 => x ^ n) atTop (𝓝 0) := by
  lift -n to ℕ using le_of_lt (neg_pos.mpr hn) with N h
  rw [← neg_pos, ← h, Nat.cast_pos] at hn
  simpa only [h, neg_neg] using tendsto_pow_neg_atTop hn.ne'

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsStrictOrderedRing.toContinuousInv₀ [ContinuousMul 𝕜] :
    ContinuousInv₀ 𝕜 := .of_nhds_one <| tendsto_order.2 <| by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨x', h₀, hxx', h₁⟩ : ∃ x', 0 < x' ∧ x ≤ x' ∧ x' < 1 :=
      ⟨max x (1 / 2), one_half_pos.trans_le (le_max_right _ _), le_max_left _ _,
        max_lt hx one_half_lt_one⟩
    filter_upwards [Ioo_mem_nhds one_pos ((one_lt_inv₀ h₀).2 h₁)] with y hy
    exact hxx'.trans_lt <| lt_inv_of_lt_inv₀ hy.1 hy.2
  · filter_upwards [Ioi_mem_nhds (inv_lt_one_of_one_lt₀ hx)] with y hy
    exact inv_lt_of_inv_lt₀ (by positivity) hy

end Semifield

/-- If a (possibly non-unital and/or non-associative) ring `R` admits a submultiplicative
nonnegative norm `norm : R → 𝕜`, where `𝕜` is a linear ordered field, and the open balls
`{ x | norm x < ε }`, `ε > 0`, form a basis of neighborhoods of zero, then `R` is a topological
ring. -/
/-
**IsTopologicalRing.of_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsTopologicalRing.of_norm {R 𝕜 : Type*} [NonUnitalNonAssocRing R] [Field 𝕜
] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace R] [IsTopologicalAdd
Group R] (norm : R -> 𝕜) (norm_nonneg : forall x, 0 <= norm x) (norm_mul_le : fo
rall x y, norm (x * y) <= norm x * norm y) (nhds_basis : (𝓝 (0 : R)).HasBasis ((
0 : 𝕜) < ·) (fun ε => { x | norm x < ε })) : IsTopologicalRing R
参数：norm : R -> 𝕜；norm_nonneg : forall x, 0 <= norm x；norm_mul_le : forall x y, n
orm (x * y) <= norm x * norm y；nhds_basis : (𝓝 (0 : R)).HasBasis ((0 : 𝕜) < ·) (
fun ε => { x | norm x < ε })。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `exists_pos_mul_lt`：exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : exist
s c : α, 0 < c ∧ b * c < a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsTopologicalRing.of_addGroup_of_nhds_zero`：IsTopologicalRing.of_addGrou
p_of_nhds_zero [IsTopologicalAddGroup R] (hmul : Tendsto (uncurry ((· * ·) : R -
> R -> R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0) …
· 使用定理 `Filter.HasBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {l
b : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} 
{pb : ι' →…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
If a (possibly non-unital and/or non-associative) ring `R` admits a submultiplic
ative
nonnegative norm `norm : R → 𝕜`, where `𝕜` is a linear ordered field, and the op
en balls
`{ x | norm x < ε }`, `ε > 0`, form a basis of neighborhoods of zero, then `R` i
s a topological
ring.
-/
theorem IsTopologicalRing.of_norm {R 𝕜 : Type*} [NonUnitalNonAssocRing R]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace R] [IsTopologicalAddGroup R] (norm : R → 𝕜)
    (norm_nonneg : ∀ x, 0 ≤ norm x) (norm_mul_le : ∀ x y, norm (x * y) ≤ norm x * norm y)
    (nhds_basis : (𝓝 (0 : R)).HasBasis ((0 : 𝕜) < ·) (fun ε ↦ { x | norm x < ε })) :
    IsTopologicalRing R := by
  have h0 : ∀ f : R → R, ∀ c ≥ (0 : 𝕜), (∀ x, norm (f x) ≤ c * norm x) →
      Tendsto f (𝓝 0) (𝓝 0) := by
    refine fun f c c0 hf ↦ (nhds_basis.tendsto_iff nhds_basis).2 fun ε ε0 ↦ ?_
    rcases exists_pos_mul_lt ε0 c with ⟨δ, δ0, hδ⟩
    refine ⟨δ, δ0, fun x hx ↦ (hf _).trans_lt ?_⟩
    exact (mul_le_mul_of_nonneg_left (le_of_lt hx) c0).trans_lt hδ
  apply IsTopologicalRing.of_addGroup_of_nhds_zero
  case hmul =>
    refine ((nhds_basis.prod nhds_basis).tendsto_iff nhds_basis).2 fun ε ε0 ↦ ?_
    refine ⟨(1, ε), ⟨one_pos, ε0⟩, fun (x, y) ⟨hx, hy⟩ => ?_⟩
    simp only at *
    calc norm (x * y) ≤ norm x * norm y := norm_mul_le _ _
    _ < ε := (mul_le_of_le_one_left (norm_nonneg _) hx.le).trans_lt hy
  case hmul_left => exact fun x => h0 _ (norm x) (norm_nonneg _) (norm_mul_le x)
  case hmul_right =>
    exact fun y => h0 (· * y) (norm y) (norm_nonneg y) fun x =>
      (norm_mul_le x y).trans_eq (mul_comm _ _)

variable {𝕜 α : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α → 𝕜}

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsStrictOrderedRing.topologicalRing : IsTopologicalRing 𝕜 :=
  .of_norm abs abs_nonneg (fun _ _ ↦ (abs_mul _ _).le) <| by
    simpa using nhds_basis_abs_sub_lt (0 : 𝕜)

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atTop` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atBot`. -/
/-
**Filter.Tendsto.atTop_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.atTop_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atTop)
 (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot
参数：hC : C < 0；hf : Tendsto f l atTop；hg : Tendsto g l (𝓝 C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_mul_pos`：Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsStrictOrderedRing.topologicalRing`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [
inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : TopologicalSpace 𝕜]   
[OrderTopology 𝕜], IsTopo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…

--- 原说明 ---
In a linearly ordered field with the order topology, if `f` tends to `Filter.atT
op` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atBot`.
-/
theorem Filter.Tendsto.atTop_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  have := hf.atTop_mul_pos (neg_pos.2 hC) hg.neg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `Filter.atTop` then `f * g` tends to `Filter.atBot`. -/
/-
**Filter.Tendsto.neg_mul_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.neg_mul_atTop {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
 (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atBot
参数：hC : C < 0；hf : Tendsto f l (𝓝 C)；hg : Tendsto g l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.Tendsto.atTop_mul_neg`：Filter.Tendsto.atTop_mul_neg {C : 𝕜} (hC :
 C < 0) (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atBot

--- 原说明 ---
In a linearly ordered field with the order topology, if `f` tends to a negative 
constant `C` and
`g` tends to `Filter.atTop` then `f * g` tends to `Filter.atBot`.
-/
theorem Filter.Tendsto.neg_mul_atTop {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atTop_mul_neg hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atBot` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atBot`. -/
/-
**Filter.Tendsto.atBot_mul_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.atBot_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atBot)
 (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot
参数：hC : 0 < C；hf : Tendsto f l atBot；hg : Tendsto g l (𝓝 C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_mul_pos`：Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atTop
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…

--- 原说明 ---
In a linearly ordered field with the order topology, if `f` tends to `Filter.atB
ot` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atBot`.
-/
theorem Filter.Tendsto.atBot_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_pos hC hg
  simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atBot` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atTop`. -/
/-
**Filter.Tendsto.atBot_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.atBot_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atBot)
 (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop
参数：hC : C < 0；hf : Tendsto f l atBot；hg : Tendsto g l (𝓝 C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.atTop_mul_neg`：Filter.Tendsto.atTop_mul_neg {C : 𝕜} (hC :
 C < 0) (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atBot
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
In a linearly ordered field with the order topology, if `f` tends to `Filter.atB
ot` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atTop`.
-/
theorem Filter.Tendsto.atBot_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_neg hC hg
  simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atBot`. -/
/-
**Filter.Tendsto.pos_mul_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.pos_mul_atBot {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
 (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atBot
参数：hC : 0 < C；hf : Tendsto f l (𝓝 C)；hg : Tendsto g l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.Tendsto.atBot_mul_pos`：Filter.Tendsto.atBot_mul_pos {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atBot

--- 原说明 ---
In a linearly ordered field with the order topology, if `f` tends to a positive 
constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atBot`.
-/
theorem Filter.Tendsto.pos_mul_atBot {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atBot_mul_pos hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atTop`. -/
/-
**Filter.Tendsto.neg_mul_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.neg_mul_atBot {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
 (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atTop
参数：hC : C < 0；hf : Tendsto f l (𝓝 C)；hg : Tendsto g l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Filter.Tendsto.atBot_mul_neg`：Filter.Tendsto.atBot_mul_neg {C : 𝕜} (hC :
 C < 0) (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f 
x * g x) l atTop

--- 原说明 ---
In a linearly ordered field with the order topology, if `f` tends to a negative 
constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atTop`.
-/
theorem Filter.Tendsto.neg_mul_atBot {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atBot_mul_neg hC hf

@[simp]
/-
**inv_atBot** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_atBot₀ : (atBot : Filter 𝕜)⁻¹ = 𝓝[<] 0 :=
  (((atBot_basis_Iio' (0 : 𝕜)).map _).comp_surjective inv_surjective).eq_of_same_basis <|
    (nhdsLT_basis _).congr (by simp) fun a ha ↦ by simp [inv_Iio₀ (inv_neg''.2 ha)]

@[simp]
/-
**inv_nhdsLT_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_nhdsLT_zero : (𝓝[<] (0 : 𝕜))⁻¹ = atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_atBot₀`：inv_atBot₀ : (atBot : Filter 𝕜)⁻¹ = 𝓝[<] 0
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma inv_nhdsLT_zero : (𝓝[<] (0 : 𝕜))⁻¹ = atBot := by
  rw [← inv_atBot₀, inv_inv]

/-- The function `x ↦ x⁻¹` tends to `-∞` on the left of `0`. -/
/-
**tendsto_inv_nhdsLT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_nhdsLT_zero : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[<] (0 : 𝕜)) atBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `inv_nhdsLT_zero`：inv_nhdsLT_zero : (𝓝[<] (0 : 𝕜))⁻¹ = atBot

--- 原说明 ---
The function `x ↦ x⁻¹` tends to `-∞` on the left of `0`.
-/
theorem tendsto_inv_nhdsLT_zero : Tendsto (fun x : 𝕜 => x⁻¹) (𝓝[<] (0 : 𝕜)) atBot :=
  inv_nhdsLT_zero.le
/-
**tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot {f : 𝕜 -> α} (h : Tendsto (f
un x => f x⁻¹) atBot l) : Tendsto f (𝓝[<] 0) l
参数：h : Tendsto (fun x => f x⁻¹) atBot l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_nhdsLT_zero`：tendsto_inv_nhdsLT_zero : Tendsto (fun x : 𝕜 =>
 x⁻¹) (𝓝[<] (0 : 𝕜)) atBot
-/
theorem tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot {f : 𝕜 → α}
    (h : Tendsto (fun x ↦ f x⁻¹) atBot l) :
    Tendsto f (𝓝[<] 0) l := by
  convert! h.comp tendsto_inv_nhdsLT_zero
  grind

/-- The function `r ↦ r⁻¹` tends to `0` on the left as `r → -∞`. -/
/-
**tendsto_inv_atBot_nhdsLT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_atBot_nhdsLT_zero : Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝[<] (0 
: 𝕜))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `inv_atBot₀`：inv_atBot₀ : (atBot : Filter 𝕜)⁻¹ = 𝓝[<] 0

--- 原说明 ---
The function `r ↦ r⁻¹` tends to `0` on the left as `r → -∞`.
-/
theorem tendsto_inv_atBot_nhdsLT_zero : Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝[<] (0 : 𝕜)) :=
  inv_atBot₀.le
/-
**tendsto_inv_atBot_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_atBot_zero : Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `tendsto_inv_atBot_nhdsLT_zero`：tendsto_inv_atBot_nhdsLT_zero : Tendsto (
fun r : 𝕜 => r⁻¹) atBot (𝓝[<] (0 : 𝕜))
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem tendsto_inv_atBot_zero : Tendsto (fun r : 𝕜 => r⁻¹) atBot (𝓝 0) :=
  tendsto_inv_atBot_nhdsLT_zero.mono_right inf_le_left
/-
**Filter.Tendsto.div_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l
 atTop) : Tendsto (fun x => f x / g x) l (𝓝 0)
参数：h : Tendsto f l (𝓝 a)；hg : Tendsto g l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsStrictOrderedRing.topologicalRing`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [
inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : TopologicalSpace 𝕜]   
[OrderTopology 𝕜], IsTopo…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atTop_zero.comp hg)
/-
**Filter.Tendsto.div_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.div_atBot {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l
 atBot) : Tendsto (fun x => f x / g x) l (𝓝 0)
参数：h : Tendsto f l (𝓝 a)；hg : Tendsto g l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsStrictOrderedRing.topologicalRing`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [
inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : TopologicalSpace 𝕜]   
[OrderTopology 𝕜], IsTopo…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atBot_zero`：tendsto_inv_atBot_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atBot (𝓝 0)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem Filter.Tendsto.div_atBot {a : 𝕜} (h : Tendsto f l (𝓝 a)) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact mul_zero a ▸ h.mul (tendsto_inv_atBot_zero.comp hg)
/-
**Filter.Tendsto.const_div_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.const_div_atTop (hg : Tendsto g l atTop) (r : 𝕜) : Tendsto 
(fun n => r / g n) l (𝓝 0)
参数：hg : Tendsto g l atTop；r : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.div_atTop`：Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto 
f l (𝓝 a)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x / g x) l (𝓝 0)
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma Filter.Tendsto.const_div_atTop (hg : Tendsto g l atTop) (r : 𝕜) :
    Tendsto (fun n ↦ r / g n) l (𝓝 0) :=
  tendsto_const_nhds.div_atTop hg
/-
**Filter.Tendsto.const_div_atBot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.const_div_atBot (hg : Tendsto g l atBot) (r : 𝕜) : Tendsto 
(fun n => r / g n) l (𝓝 0)
参数：hg : Tendsto g l atBot；r : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.div_atBot`：Filter.Tendsto.div_atBot {a : 𝕜} (h : Tendsto 
f l (𝓝 a)) (hg : Tendsto g l atBot) : Tendsto (fun x => f x / g x) l (𝓝 0)
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma Filter.Tendsto.const_div_atBot (hg : Tendsto g l atBot) (r : 𝕜) :
    Tendsto (fun n ↦ r / g n) l (𝓝 0) :=
  tendsto_const_nhds.div_atBot hg
/-
**Filter.Tendsto.inv_tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.inv_tendsto_atBot (h : Tendsto f l atBot) : Tendsto f⁻¹ l (
𝓝 0)
参数：h : Tendsto f l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atBot_zero`：tendsto_inv_atBot_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atBot (𝓝 0)
-/
theorem Filter.Tendsto.inv_tendsto_atBot (h : Tendsto f l atBot) : Tendsto f⁻¹ l (𝓝 0) :=
  tendsto_inv_atBot_zero.comp h
/-
**Filter.Tendsto.inv_tendsto_nhdsLT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.inv_tendsto_nhdsLT_zero (h : Tendsto f l (𝓝[<] 0)) : Tendst
o f⁻¹ l atBot
参数：h : Tendsto f l (𝓝[<] 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_nhdsLT_zero`：tendsto_inv_nhdsLT_zero : Tendsto (fun x : 𝕜 =>
 x⁻¹) (𝓝[<] (0 : 𝕜)) atBot
-/
theorem Filter.Tendsto.inv_tendsto_nhdsLT_zero (h : Tendsto f l (𝓝[<] 0)) : Tendsto f⁻¹ l atBot :=
  tendsto_inv_nhdsLT_zero.comp h

/-- If `g` tends to zero and there exists a constant `C : 𝕜` such that eventually `|f x| ≤ C`,
  then the product `f * g` tends to zero. -/
/-
**bdd_le_mul_tendsto_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bdd_le_mul_tendsto_zero' {f g : α -> 𝕜} (C : 𝕜) (hf : forallᶠ x in l, |f x
| <= C) (hg : Tendsto g l (𝓝 0)) : Tendsto (fun x => f x * g x) l (𝓝 0)
参数：C : 𝕜；hf : forallᶠ x in l, |f x| <= C；hg : Tendsto g l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_zero_iff_abs_tendsto_zero`：∀ {G : Type u_1} [inst : TopologicalS
pace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G
]   [OrderTopology G] {…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.abs`：∀ {G : Type u_1} [inst : TopologicalSpace G] [inst_1
 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [OrderTopol
ogy G] {…
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsStrictOrderedRing.topologicalRing`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [
inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : TopologicalSpace 𝕜]   
[OrderTopology 𝕜], IsTopo…
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|

--- 原说明 ---
If `g` tends to zero and there exists a constant `C : 𝕜` such that eventually `|
f x| ≤ C`,
  then the product `f * g` tends to zero.
-/
theorem bdd_le_mul_tendsto_zero' {f g : α → 𝕜} (C : 𝕜) (hf : ∀ᶠ x in l, |f x| ≤ C)
    (hg : Tendsto g l (𝓝 0)) : Tendsto (fun x ↦ f x * g x) l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hC : Tendsto (fun x ↦ |C * g x|) l (𝓝 0) := by
    convert! (hg.const_mul C).abs
    simp_rw [mul_zero, abs_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
  · filter_upwards [hf] with x _ using abs_nonneg _
  · filter_upwards [hf] with x hx
    simp only [comp_apply, abs_mul]
    exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (abs_nonneg _)

/-- If `g` tends to zero and there exist constants `b B : 𝕜` such that eventually `b ≤ f x| ≤ B`,
  then the product `f * g` tends to zero. -/
/-
**bdd_le_mul_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bdd_le_mul_tendsto_zero {f g : α -> 𝕜} {b B : 𝕜} (hb : forallᶠ x in l, b <
= f x) (hB : forallᶠ x in l, f x <= B) (hg : Tendsto g l (𝓝 0)) : Tendsto (fun x
 => f x * g x) l (𝓝 0)
参数：hb : forallᶠ x in l, b <= f x；hB : forallᶠ x in l, f x <= B；hg : Tendsto g l 
(𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `neg_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a
 : α), -a ≤ |a|
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `bdd_le_mul_tendsto_zero'`：bdd_le_mul_tendsto_zero' {f g : α -> 𝕜} (C : 𝕜
) (hf : forallᶠ x in l, |f x| <= C) (hg : Tendsto g l (𝓝 0)) : Tendsto (fun x =>
 f x * g x) l …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
If `g` tends to zero and there exist constants `b B : 𝕜` such that eventually `b
 ≤ f x| ≤ B`,
  then the product `f * g` tends to zero.
-/
theorem bdd_le_mul_tendsto_zero {f g : α → 𝕜} {b B : 𝕜} (hb : ∀ᶠ x in l, b ≤ f x)
    (hB : ∀ᶠ x in l, f x ≤ B) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x ↦ f x * g x) l (𝓝 0) := by
  set C := max |b| |B|
  have hbC : -C ≤ b := neg_le.mpr (le_max_of_le_left (neg_le_abs b))
  have hBC : B ≤ C := le_max_of_le_right (le_abs_self B)
  apply bdd_le_mul_tendsto_zero' C _ hg
  filter_upwards [hb, hB]
  exact fun x hbx hBx ↦ abs_le.mpr ⟨hbC.trans hbx, hBx.trans hBC⟩

/-- If `g` tends to `atTop` and there exist constants `b B : 𝕜` such that eventually
  `b ≤ f x| ≤ B`, then the quotient `f / g` tends to zero. -/
/-
**tendsto_bdd_div_atTop_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_bdd_div_atTop_nhds_zero {f g : α -> 𝕜} {b B : 𝕜} (hb : forallᶠ x i
n l, b <= f x) (hB : forallᶠ x in l, f x <= B) (hg : Tendsto g l atTop) : Tendst
o (fun x => f x / g x) l (𝓝 0)
参数：hb : forallᶠ x in l, b <= f x；hB : forallᶠ x in l, f x <= B；hg : Tendsto g l 
atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `bdd_le_mul_tendsto_zero`：bdd_le_mul_tendsto_zero {f g : α -> 𝕜} {b B : 𝕜
} (hb : forallᶠ x in l, b <= f x) (hB : forallᶠ x in l, f x <= B) (hg : Tendsto 
g l (𝓝 0)) : …
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)

--- 原说明 ---
If `g` tends to `atTop` and there exist constants `b B : 𝕜` such that eventually
  `b ≤ f x| ≤ B`, then the quotient `f / g` tends to zero.
-/
theorem tendsto_bdd_div_atTop_nhds_zero {f g : α → 𝕜} {b B : 𝕜}
    (hb : ∀ᶠ x in l, b ≤ f x) (hB : ∀ᶠ x in l, f x ≤ B) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x / g x) l (𝓝 0) := by
  simp only [div_eq_mul_inv]
  exact bdd_le_mul_tendsto_zero hb hB hg.inv_tendsto_atTop
/-
**tendsto_const_mul_zpow_atTop_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_mul_zpow_atTop_zero {n : Int} {c : 𝕜} (hn : n < 0) : Tendsto
 (fun x => c * x ^ n) atTop (𝓝 0)
参数：hn : n < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsStrictOrderedRing.topologicalRing`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [
inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : TopologicalSpace 𝕜]   
[OrderTopology 𝕜], IsTopo…
· 使用定理 `tendsto_zpow_atTop_zero`：tendsto_zpow_atTop_zero {n : Int} (hn : n < 0) 
: Tendsto (fun x : 𝕜 => x ^ n) atTop (𝓝 0)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem tendsto_const_mul_zpow_atTop_zero {n : ℤ} {c : 𝕜} (hn : n < 0) :
    Tendsto (fun x => c * x ^ n) atTop (𝓝 0) :=
  mul_zero c ▸ Filter.Tendsto.const_mul c (tendsto_zpow_atTop_zero hn)
/-
**tendsto_const_mul_pow_nhds_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_mul_pow_nhds_iff' {n : Nat} {c d : 𝕜} : Tendsto (fun x : 𝕜 =
> c * x ^ n) atTop (𝓝 d) ↔ (c = 0 ∨ n = 0) ∧ c = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
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
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_const_mul_pow_atBot_iff`：tendsto_const_mul_pow_atBot_iff 
{c : α} {n : Nat} : Tendsto (fun x => c * x ^ n) atTop atBot ↔ n != 0 ∧ c < 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_tendsto_nhds_of_tendsto_atBot`：not_tendsto_nhds_of_tendsto_atBot (hf
 : Tendsto f l atBot) (a : α) : ¬Tendsto f l (𝓝 a)
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
（共 41 条，此处仅展示前 30 条）
-/
theorem tendsto_const_mul_pow_nhds_iff' {n : ℕ} {c d : 𝕜} :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ (c = 0 ∨ n = 0) ∧ c = d := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [tendsto_const_nhds_iff]
  rcases lt_trichotomy c 0 with (hc | rfl | hc)
  · have := tendsto_const_mul_pow_atBot_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atBot this, hc.ne, hn]
  · simp [tendsto_const_nhds_iff]
  · have := tendsto_const_mul_pow_atTop_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atTop this, hc.ne', hn]
/-
**tendsto_const_mul_pow_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_mul_pow_nhds_iff {n : Nat} {c d : 𝕜} (hc : c != 0) : Tendsto
 (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_const_mul_pow_nhds_iff {n : ℕ} {c d : 𝕜} (hc : c ≠ 0) :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d := by
  simp [tendsto_const_mul_pow_nhds_iff', hc]
/-
**tendsto_const_mul_zpow_atTop_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_mul_zpow_atTop_nhds_iff {n : Int} {c d : 𝕜} (hc : c != 0) : 
Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d ∨ n < 0 ∧ d = 0
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `tendsto_const_mul_pow_nhds_iff`：tendsto_const_mul_pow_nhds_iff {n : Nat}
 {c d : 𝕜} (hc : c != 0) : Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 
∧ c = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.negSucc_lt_zero`：∀ (n : ℕ), Int.negSucc n < 0
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `tendsto_const_mul_zpow_atTop_zero`：tendsto_const_mul_zpow_atTop_zero {n 
: Int} {c : 𝕜} (hn : n < 0) : Tendsto (fun x => c * x ^ n) atTop (𝓝 0)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem tendsto_const_mul_zpow_atTop_nhds_iff {n : ℤ} {c d : 𝕜} (hc : c ≠ 0) :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d ∨ n < 0 ∧ d = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases n with
    | ofNat n =>
      left
      simpa [tendsto_const_mul_pow_nhds_iff hc] using h
    | negSucc n =>
      have hn := Int.negSucc_lt_zero n
      exact Or.inr ⟨hn, tendsto_nhds_unique h (tendsto_const_mul_zpow_atTop_zero hn)⟩
  · rcases h with h | h
    · simp only [h.left, h.right, zpow_zero, mul_one]
      exact tendsto_const_nhds
    · exact h.2.symm ▸ tendsto_const_mul_zpow_atTop_zero h.1
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsStrictOrderedRing.toIsTopologicalDivisionRing :
    IsTopologicalDivisionRing 𝕜 := ⟨⟩

-- TODO: generalize to a `GroupWithZero`
/-
**comap_mulLeft_nhdsGT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_mulLeft_nhdsGT_zero {x : 𝕜} (hx : 0 < x) : comap (x * ·) (𝓝[>] 0) = 
𝓝[>] 0
参数：hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Set.preimage_const_mul_Ioi₀`：preimage_const_mul_Ioi₀ (a : G₀) (h : 0 < c
) : (c * ·) ⁻¹' Ioi a = Ioi (a / c)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Homeomorph.comap_nhds_eq`：comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (
𝓝 y) = 𝓝 (h.symm y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_mulLeft_nhdsGT_zero {x : 𝕜} (hx : 0 < x) : comap (x * ·) (𝓝[>] 0) = 𝓝[>] 0 := by
  rw [nhdsWithin, comap_inf, comap_principal, preimage_const_mul_Ioi₀ _ hx, zero_div]
  congr 1
  refine ((Homeomorph.mulLeft₀ x hx.ne').comap_nhds_eq _).trans ?_
  simp
/-
**eventually_nhdsGT_zero_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_nhdsGT_zero_mul_left {x : 𝕜} (hx : 0 < x) {p : 𝕜 -> Prop} (h : 
forallᶠ ε in 𝓝[>] 0, p ε) : forallᶠ ε in 𝓝[>] 0, p (x * ε)
参数：hx : 0 < x；h : forallᶠ ε in 𝓝[>] 0, p ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_mulLeft_nhdsGT_zero`：comap_mulLeft_nhdsGT_zero {x : 𝕜} (hx : 0 < x
) : comap (x * ·) (𝓝[>] 0) = 𝓝[>] 0
· 使用定理 `Filter.Eventually.comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} 
{p : β → Prop},   (∀ᶠ (b : β) in g, p b) → ∀ (f : α → β), ∀ᶠ (a : α) in Filter.c
omap f g, p (…
-/
theorem eventually_nhdsGT_zero_mul_left {x : 𝕜} (hx : 0 < x) {p : 𝕜 → Prop}
    (h : ∀ᶠ ε in 𝓝[>] 0, p ε) : ∀ᶠ ε in 𝓝[>] 0, p (x * ε) := by
  rw [← comap_mulLeft_nhdsGT_zero hx]
  exact h.comap fun ε => x * ε
