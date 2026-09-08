/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.GroupTheory.Subsemigroup.Center

/-!
# Centers of monoids

## Main definitions

* `Submonoid.center`: the center of a monoid
* `AddSubmonoid.center`: the center of an additive monoid

We provide `Subgroup.center`, `AddSubgroup.center`, `Subsemiring.center`, and `Subring.center` in
other files.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Finset

namespace Submonoid

section MulOneClass

variable (M : Type*) [MulOneClass M]

/-- The center of a multiplication with unit `M` is the set of elements that commute with everything
in `M` -/
@[to_additive
/-- The center of an addition with zero `M` is the set of elements that commute with everything in
`M` -/]
/-
**Submonoid.center** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：center : Submonoid M where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.one_mem_center`：one_mem_center : (1 : M) in Set.center M where comm 
_
-/
def center : Submonoid M where
  carrier := Set.center M
  one_mem' := Set.one_mem_center
  mul_mem' := Set.mul_mem_center

@[to_additive]
/-
**Submonoid.coe_center** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_center : ↑(center M) = Set.center M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_center : ↑(center M) = Set.center M :=
  rfl

@[to_additive (attr := simp) AddSubmonoid.center_toAddSubsemigroup]
/-
**Submonoid.center_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：center_toSubsemigroup : (center M).toSubsemigroup = Subsemigroup.center M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center_toSubsemigroup : (center M).toSubsemigroup = Subsemigroup.center M :=
  rfl
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M α : Type*} [Monoid M] [MulAction M α] :
    SMulCommClass ↥(Submonoid.center M) M α where
  smul_comm c r v := by
    have := Semigroup.mem_center_iff.1 c.2
    simp_rw [Submonoid.smul_def, smul_smul, this]
/-
**Submonoid.** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M α : Type*} [Monoid M] [MulAction M α] :
    SMulCommClass M (Submonoid.center M) α :=
  SMulCommClass.symm (Submonoid.center M) M α

variable {M}

/-- The center of a multiplication with unit is commutative and associative.

This is not an instance as it forms a non-defeq diamond with `Submonoid.toMonoid` in the `npow`
field. -/
@[to_additive /-- The center of an addition with zero is commutative and associative. -/]
/-
**Submonoid.center.commMonoid'** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid.center`。
形式化陈述：{M : Type u_1} → [inst : MulOneClass M] → CommMonoid ↥(Submonoid.center M)
参数：Submonoid.center M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a multiplication with unit is commutative and associative.

This is not an instance as it forms a non-defeq diamond with `Submonoid.toMonoid
` in the `npow`
field.
-/
abbrev center.commMonoid' : CommMonoid (center M) :=
  { (center M).toMulOneClass, Subsemigroup.center.commSemigroup with }

@[to_additive]
/-
**Submonoid.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {M : Type u_1} [inst : MulOneClass M] {N : Type u_2} [inst_1 : MulOneCla
ss N],   Submonoid.center (M × N) = (Submonoid.center M).prod (Submonoid.center 
N)
参数：M × N；Submonoid.center M；Submonoid.center N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_prod`：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 
: Mul N], Set.center (M × N) = Set.center M ×ˢ Set.center N
-/
protected theorem center_prod {N : Type*} [MulOneClass N] :
    center (M × N) = prod (center M) (center N) :=
  SetLike.coe_injective Set.center_prod

@[to_additive]
/-
**Submonoid.center_pi** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：∀ {ι : Type u_2} {M : ι → Type u_3} [inst : (i : ι) → MulOneClass (M i)], 
  Submonoid.center ((i : ι) → M i) = Submonoid.pi Set.univ fun i => Submonoid.ce
nter (M i)
参数：i : ι；M i；(i : ι) → M i；M i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_pi`：∀ {ι : Type u_2} {A : ι → Type u_3} [inst : (i : ι) → Mul
 (A i)],   Set.center ((i : ι) → A i) = Set.univ.pi fun i => Set.center (A i)
-/
protected theorem center_pi {ι : Type*} {M : ι → Type*} [Π i, MulOneClass (M i)] :
    center (Π i, M i) = pi .univ fun i ↦ center (M i) :=
  SetLike.coe_injective Set.center_pi

end MulOneClass

section Monoid

variable {M} [Monoid M]

/-- The center of a monoid is commutative. -/
@[to_additive]
/-
**Submonoid.center.commMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid.center`。
形式化陈述：{M : Type u_1} → [inst : Monoid M] → CommMonoid ↥(Submonoid.center M)
参数：Submonoid.center M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a monoid is commutative.
-/
instance center.commMonoid : CommMonoid (center M) :=
  { (center M).toMonoid, Subsemigroup.center.commSemigroup with }

-- no instance diamond, unlike the primed version
/-
**Submonoid.** 是 Mathlib 中的一个示例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : center.commMonoid.toMonoid = Submonoid.toMonoid (center M) := by
  with_reducible_and_instances rfl

@[to_additive]
/-
**Submonoid.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_center_iff {z : M} : z in center M ↔ forall g, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

@[to_additive]
/-
**Submonoid.decidableMemCenter** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：decidableMemCenter (a) [Decidable <| forall b : M, b * a = a * b] : Decida
ble (a in center M)
参数：a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mem_center_iff`：mem_center_iff {z : M} : z in center M ↔ foral
l g, g * z = z * g
-/
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] : Decidable (a ∈ center M) :=
  decidable_of_iff' _ mem_center_iff



/-- The center of a monoid acts commutatively on that monoid. -/
/-
**Submonoid.center.smulCommClass_left** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.cente
r`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M], SMulCommClass (↥(Submonoid.center M)) 
M M
参数：↥(Submonoid.center M)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.left_comm`：∀ {S : Type u_3} [inst : Semigroup S] {a b : S}, Comm
ute a b → ∀ (c : S), a * (b * c) = b * (a * c)
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
The center of a monoid acts commutatively on that monoid.
-/
instance center.smulCommClass_left : SMulCommClass (center M) M M where
  smul_comm m x y := Commute.left_comm (m.prop.comm x) y

/-- The center of a monoid acts commutatively on that monoid. -/
/-
**Submonoid.center.smulCommClass_right** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.cent
er`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M], SMulCommClass M (↥(Submonoid.center M)
) M
参数：↥(Submonoid.center M)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Submonoid.center.smulCommClass_left`：∀ {M : Type u_1} [inst : Monoid M],
 SMulCommClass (↥(Submonoid.center M)) M M

--- 原说明 ---
The center of a monoid acts commutatively on that monoid.
-/
instance center.smulCommClass_right : SMulCommClass M (center M) M :=
  SMulCommClass.symm _ _ _

/-! Note that `smulCommClass (center M) (center M) M` is already implied by
`Submonoid.smulCommClass_right` -/

/-
**Submonoid.** 是 Mathlib 中的一个示例，位于命名空间 `Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that `smulCommClass (center M) (center M) M` is already implied by
`Submonoid.smulCommClass_right`
-/
example : SMulCommClass (center M) (center M) M := by infer_instance

end Monoid

section

variable (M : Type*) [CommMonoid M]

@[simp]
/-
**Submonoid.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：center_eq_top : center M = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_eq_univ`：center_eq_univ : center M = univ
-/
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)

end

end Submonoid

variable (M)

/-- For a monoid, the units of the center inject into the center of the units. This is not an
equivalence in general; one case where this holds is for groups with zero, which is covered in
`centerUnitsEquivUnitsCenter`. -/
@[to_additive (attr := simps! apply_coe_val)
  /-- For an additive monoid, the units of the center inject into the center of the units. -/]
/-
**unitsCenterToCenterUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：unitsCenterToCenterUnits [Monoid M] : (Submonoid.center M)ˣ ->* Submonoid.
center (Mˣ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def unitsCenterToCenterUnits [Monoid M] : (Submonoid.center M)ˣ →* Submonoid.center (Mˣ) :=
  (Units.map (Submonoid.center M).subtype).codRestrict _ <|
      fun u ↦ Submonoid.mem_center_iff.mpr <|
        fun r ↦ Units.ext <| by
        rw [Units.val_mul, Units.coe_map, Submonoid.coe_subtype, Units.val_mul, Units.coe_map,
          Submonoid.coe_subtype, u.1.prop.comm r]

@[to_additive]
/-
**unitsCenterToCenterUnits_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unitsCenterToCenterUnits_injective [Monoid M] : Function.Injective (unitsC
enterToCenterUnits M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem unitsCenterToCenterUnits_injective [Monoid M] :
    Function.Injective (unitsCenterToCenterUnits M) :=
  fun _a _b h => Units.ext <| Subtype.ext <| congr_arg (Units.val ∘ Subtype.val) h

section congr

variable {M} {N : Type*}

/-
**_root_.MulEquivClass.apply_mem_center** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] theorem _root_.MulEquivClass.apply_mem_center {F} [EquivLike F M N] [Mul M] [Mul N]
    [MulEquivClass F M N] (e : F) {x : M} (hx : x ∈ Set.center M) : e x ∈ Set.center N := by
  let e := MulEquivClass.toMulEquiv e
  change e x ∈ Set.center N
  constructor <;>
  (intros; apply e.symm.injective; simp only
    [map_mul, e.symm_apply_apply, (hx.comm _).eq, (isMulCentral_iff _).mp hx, ← hx.right_comm])
/-
**_root_.MulEquivClass.apply_mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] theorem _root_.MulEquivClass.apply_mem_center_iff {F} [EquivLike F M N]
    [Mul M] [Mul N] [MulEquivClass F M N] (e : F) {x : M} :
    e x ∈ Set.center N ↔ x ∈ Set.center M :=
  ⟨(by simpa using MulEquivClass.apply_mem_center (MulEquivClass.toMulEquiv e).symm ·),
    MulEquivClass.apply_mem_center e⟩

/-- The center of isomorphic magmas are isomorphic. -/
@[to_additive (attr := simps) /-- The center of isomorphic additive magmas are isomorphic. -/]
/-
**Subsemigroup.centerCongr** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subsemigroup.centerCongr [Mul M] [Mul N] (e : M ≃* N) : center M ≃* center
 N where toFun r
参数：e : M ≃* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of isomorphic magmas are isomorphic.
-/
def Subsemigroup.centerCongr [Mul M] [Mul N] (e : M ≃* N) : center M ≃* center N where
  toFun r := ⟨e r, MulEquivClass.apply_mem_center e r.2⟩
  invFun s := ⟨e.symm s, MulEquivClass.apply_mem_center e.symm s.2⟩
  left_inv _ := Subtype.ext (e.left_inv _)
  right_inv _ := Subtype.ext (e.right_inv _)
  map_mul' _ _ := Subtype.ext (map_mul ..)

/-- The center of isomorphic monoids are isomorphic. -/
@[to_additive (attr := simps!) /-- The center of isomorphic additive monoids are isomorphic. -/]
/-
**Submonoid.centerCongr** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.centerCongr [MulOneClass M] [MulOneClass N] (e : M ≃* N) : cente
r M ≃* center N
参数：e : M ≃* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of isomorphic monoids are isomorphic.
-/
def Submonoid.centerCongr [MulOneClass M] [MulOneClass N] (e : M ≃* N) : center M ≃* center N :=
  Subsemigroup.centerCongr e
/-
**MulOpposite.op_mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {M : Type u_2} [inst : Mul M] {x : M}, MulOpposite.op x ∈ Set.center Mᵐᵒ
ᵖ ↔ x ∈ Set.center M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[to_additive] theorem MulOpposite.op_mem_center_iff [Mul M] {x : M} :
    op x ∈ Set.center Mᵐᵒᵖ ↔ x ∈ Set.center M := by
  simp_rw [Set.mem_center_iff, isMulCentral_iff, MulOpposite.forall, ← op_mul, op_inj]; aesop
/-
**MulOpposite.unop_mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：∀ {M : Type u_2} [inst : Mul M] {x : Mᵐᵒᵖ}, MulOpposite.unop x ∈ Set.cente
r M ↔ x ∈ Set.center Mᵐᵒᵖ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MulOpposite.op_mem_center_iff`：∀ {M : Type u_2} [inst : Mul M] {x : M}, 
MulOpposite.op x ∈ Set.center Mᵐᵒᵖ ↔ x ∈ Set.center M
-/
@[to_additive] theorem MulOpposite.unop_mem_center_iff [Mul M] {x : Mᵐᵒᵖ} :
    unop x ∈ Set.center M ↔ x ∈ Set.center Mᵐᵒᵖ :=
  op_mem_center_iff.symm

/-- The center of a magma is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps)
/-- The center of an additive magma is isomorphic to the center of its opposite. -/]
/-
**Subsemigroup.centerToMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subsemigroup.centerToMulOpposite [Mul M] : center M ≃* center Mᵐᵒᵖ where t
oFun r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Subsemigroup.centerToMulOpposite [Mul M] : center M ≃* center Mᵐᵒᵖ where
  toFun r := ⟨_, MulOpposite.op_mem_center_iff.mpr r.2⟩
  invFun r := ⟨_, MulOpposite.unop_mem_center_iff.mpr r.2⟩
  map_mul' r _ := Subtype.ext (congr_arg MulOpposite.op <| r.2.1 _)

/-- The center of a monoid is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps!)
/-- The center of an additive monoid is isomorphic to the center of its opposite. -/]
/-
**Submonoid.centerToMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submonoid.centerToMulOpposite [MulOneClass M] : center M ≃* center Mᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Submonoid.centerToMulOpposite [MulOneClass M] : center M ≃* center Mᵐᵒᵖ :=
  Subsemigroup.centerToMulOpposite

end congr

