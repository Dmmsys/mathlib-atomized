/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.Instances.ZMultiples

/-!
# The additive circle over `ℝ`

Results specific to the additive circle over `ℝ`.
-/

@[expose] public section


noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace Topology

namespace AddCircle

variable (p : ℝ)

/-
**AddCircle.pathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
形式化陈述：pathConnectedSpace : PathConnectedSpace AddCircle p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pathConnectedSpace : PathConnectedSpace <| AddCircle p :=
  inferInstanceAs <| PathConnectedSpace (Quotient _)

/-- The "additive circle" `ℝ ⧸ ℤ ∙ p` is compact. -/
/-
**AddCircle.compactSpace** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
形式化陈述：compactSpace [Fact (0 < p)] : CompactSpace AddCircle p
参数：0 < p。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
· 使用定理 `AddCircle.coe_image_Icc_eq`：coe_image_Icc_eq : ((↑) : 𝕜 -> AddCircle p) 
'' Icc a (a + p) = univ
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `AddCircle.continuous_mk'`：∀ {𝕜 : Type u_1} [inst : AddCommGroup 𝕜] (p : 
𝕜) [inst_1 : TopologicalSpace 𝕜],   Continuous ⇑(QuotientAddGroup.mk' (AddSubgro
up.zmultiples …

--- 原说明 ---
The "additive circle" `ℝ ⧸ ℤ ∙ p` is compact.
-/
instance compactSpace [Fact (0 < p)] : CompactSpace <| AddCircle p := by
  rw [← isCompact_univ_iff, ← coe_image_Icc_eq p 0]
  exact isCompact_Icc.image (AddCircle.continuous_mk' p)

/-- The action on `ℝ` by right multiplication of its the subgroup `zmultiples p` (the multiples of
`p:ℝ`) is properly discontinuous. -/
/-
**AddCircle.** 是 Mathlib 中的一个实例，位于命名空间 `AddCircle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on `ℝ` by right multiplication of its the subgroup `zmultiples p` (th
e multiples of
`p:ℝ`) is properly discontinuous.
-/
instance : ProperlyDiscontinuousVAdd (zmultiples p).op ℝ :=
  (zmultiples p).properlyDiscontinuousVAdd_opposite_of_tendsto_cofinite
    (AddSubgroup.tendsto_zmultiples_subtype_cofinite p)

end AddCircle

section UnitAddCircle

/-- The unit circle `ℝ ⧸ ℤ`. -/
/-
**UnitAddCircle** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UnitAddCircle
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit circle `ℝ ⧸ ℤ`.
-/
abbrev UnitAddCircle :=
  AddCircle (1 : ℝ)

/-- The product indexed by `d` of copies of the unit circle. -/
/-
**UnitAddTorus** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UnitAddTorus (d : Type*)
参数：d : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product indexed by `d` of copies of the unit circle.
-/
abbrev UnitAddTorus (d : Type*) := d → UnitAddCircle

end UnitAddCircle

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The `AddMonoidHom` from `ZMod N` to `ℝ / ℤ` sending `j mod N` to `j / N mod 1`. -/
/-
**ZMod.toAddCircle** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：toAddCircle : ZMod N ->+ UnitAddCircle
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `AddMonoidHom` from `ZMod N` to `ℝ / ℤ` sending `j mod N` to `j / N mod 1`.
-/
noncomputable def toAddCircle : ZMod N →+ UnitAddCircle :=
  lift N ⟨AddMonoidHom.mk' (fun j ↦ ↑(j / N : ℝ)) (by simp [add_div]),
    by simp [div_self (NeZero.ne _)]⟩
/-
**ZMod.toAddCircle_intCast** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：toAddCircle_intCast (j : Int) : toAddCircle (j : ZMod N) = ↑(j / N : Real)
参数：j : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.lift_coe`：lift_coe (x : Int) : lift n f (x : ZMod n) = f.val x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddMonoidHom.mk'_apply`：∀ {M : Type u_4} {G : Type u_7} [inst : AddGroup
 G] [inst_1 : AddZeroClass M] (f : M → G)   (map_add : ∀ (a b : M), f (a + b) = 
f a + f b), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toAddCircle_intCast (j : ℤ) :
    toAddCircle (j : ZMod N) = ↑(j / N : ℝ) := by
  simp [toAddCircle]
/-
**ZMod.toAddCircle_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：toAddCircle_natCast (j : Nat) : toAddCircle (j : ZMod N) = ↑(j / N : Real)
参数：j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ZMod.toAddCircle_intCast`：toAddCircle_intCast (j : Int) : toAddCircle (j
 : ZMod N) = ↑(j / N : Real)
-/
lemma toAddCircle_natCast (j : ℕ) :
    toAddCircle (j : ZMod N) = ↑(j / N : ℝ) := by
  simpa using toAddCircle_intCast (N := N) j

/--
Explicit formula for `toCircle j`. Note that this is "evil" because it uses `ZMod.val`. Where
possible, it is recommended to lift `j` to `ℤ` and use `toAddCircle_intCast` instead.
-/
/-
**ZMod.toAddCircle_apply** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：toAddCircle_apply (j : ZMod N) : toAddCircle j = ↑(j.val / N : Real)
参数：j : ZMod N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ZMod.toAddCircle_natCast`：toAddCircle_natCast (j : Nat) : toAddCircle (j
 : ZMod N) = ↑(j / N : Real)
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a

--- 原说明 ---
Explicit formula for `toCircle j`. Note that this is "evil" because it uses `ZMo
d.val`. Where
possible, it is recommended to lift `j` to `ℤ` and use `toAddCircle_intCast` ins
tead.
-/
lemma toAddCircle_apply (j : ZMod N) :
    toAddCircle j = ↑(j.val / N : ℝ) := by
  rw [← toAddCircle_natCast, natCast_zmod_val]

variable (N) in
/-
**ZMod.toAddCircle_injective** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：toAddCircle_injective : Function.Injective (toAddCircle : ZMod N -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ZMod.val_injective`：val_injective (n : Nat) [NeZero n] : Function.Inject
ive (val : ZMod n -> Nat)
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `div_left_inj'`：div_left_inj' (hc : c != 0) : a / c = b / c ↔ a = b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `AddCircle.coe_eq_coe_iff_of_mem_Ico`：coe_eq_coe_iff_of_mem_Ico {x y : 𝕜}
 (hx : x in Ico a (a + p)) (hy : y in Ico a (a + p)) : (x : AddCircle p) = y ↔ x
 = y
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用引理 `ZMod.toAddCircle_apply`：toAddCircle_apply (j : ZMod N) : toAddCircle j =
 ↑(j.val / N : Real)
-/
lemma toAddCircle_injective : Function.Injective (toAddCircle : ZMod N → _) := by
  intro x y hxy
  have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos _)
  rwa [toAddCircle_apply, toAddCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico,
    div_left_inj' this.ne', Nat.cast_inj, (val_injective N).eq_iff] at hxy <;>
  exact ⟨by positivity, by simpa only [zero_add, div_lt_one this, Nat.cast_lt] using val_lt _⟩
/-
**ZMod.toAddCircle_inj** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {j k : ZMod N}, ZMod.toAddCircle j = ZMod.toAd
dCircle k ↔ j = k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用引理 `ZMod.toAddCircle_injective`：toAddCircle_injective : Function.Injective (
toAddCircle : ZMod N -> _)
-/
@[simp] lemma toAddCircle_inj {j k : ZMod N} : toAddCircle j = toAddCircle k ↔ j = k :=
  (toAddCircle_injective N).eq_iff
/-
**ZMod.toAddCircle_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {j : ZMod N}, ZMod.toAddCircle j = 0 ↔ j = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `ZMod.toAddCircle_injective`：toAddCircle_injective : Function.Injective (
toAddCircle : ZMod N -> _)
-/
@[simp] lemma toAddCircle_eq_zero {j : ZMod N} : toAddCircle j = 0 ↔ j = 0 :=
  map_eq_zero_iff _ (toAddCircle_injective N)

end ZMod

