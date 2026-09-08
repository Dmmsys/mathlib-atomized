/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Submonoid.Center

/-!
# Centers of subgroups

-/

@[expose] public section

assert_not_exists MonoidWithZero Multiset

variable {G : Type*} [Group G]

namespace Subgroup

variable (G)

/-- The center of a group `G` is the set of elements that commute with everything in `G` -/
@[to_additive
      /-- The center of an additive group `G` is the set of elements that commute with
      everything in `G` -/]
/-
**Subgroup.center** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：center : Subgroup G where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def center : Subgroup G where
  __ := Submonoid.center G
  inv_mem' := Set.inv_mem_center

@[to_additive]
/-
**Subgroup.coe_center** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_center : ↑(center G) = Set.center G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_center : ↑(center G) = Set.center G :=
  rfl

@[to_additive (attr := simp)]
/-
**Subgroup.center_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：center_toSubmonoid : (center G).toSubmonoid = Submonoid.center G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem center_toSubmonoid : (center G).toSubmonoid = Submonoid.center G :=
  rfl
/-
**Subgroup.center.isMulCommutative** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.center`。
形式化陈述：∀ (G : Type u_1) [inst : Group G], IsMulCommutative ↥(Subgroup.center G)
参数：G : Type u_1；Subgroup.center G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance center.isMulCommutative : IsMulCommutative (center G) :=
  ⟨⟨fun a b => Subtype.ext (b.2.comm a).symm⟩⟩

variable {G} in
/-- The center of isomorphic groups are isomorphic. -/
@[to_additive (attr := simps!) /-- The center of isomorphic additive groups are isomorphic. -/]
/-
**Subgroup.centerCongr** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：centerCongr {H} [Group H] (e : G ≃* H) : center G ≃* center H
参数：e : G ≃* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of isomorphic groups are isomorphic.
-/
def centerCongr {H} [Group H] (e : G ≃* H) : center G ≃* center H := Submonoid.centerCongr e

/-- The center of a group is isomorphic to the center of its opposite. -/
@[to_additive (attr := simps!)
/-- The center of an additive group is isomorphic to the center of its opposite. -/]
/-
**Subgroup.centerToMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：centerToMulOpposite : center G ≃* center Gᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def centerToMulOpposite : center G ≃* center Gᵐᵒᵖ := Submonoid.centerToMulOpposite

variable {G}

@[to_additive]
/-
**Subgroup.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_center_iff {z : G} : z in center G ↔ forall g, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_center_iff {z : G} : z ∈ center G ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl
/-
**Subgroup.decidableMemCenter** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：decidableMemCenter (z : G) [Decidable (forall g, g * z = z * g)] : Decidab
le (z in center G)
参数：z : G；forall g, g * z = z * g。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
-/
instance decidableMemCenter (z : G) [Decidable (∀ g, g * z = z * g)] : Decidable (z ∈ center G) :=
  decidable_of_iff' _ mem_center_iff

@[to_additive]
/-
**Subgroup.centerCharacteristic** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：centerCharacteristic : (center G).Characteristic
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.characteristic_iff_comap_le`：characteristic_iff_comap_le : H.Ch
aracteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom <= H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
-/
instance centerCharacteristic : (center G).Characteristic := by
  refine characteristic_iff_comap_le.mpr fun ϕ g hg => ?_
  rw [mem_center_iff]
  intro h
  rw [← ϕ.injective.eq_iff, map_mul, map_mul]
  exact (hg.comm (ϕ h)).symm

@[to_additive]
/-
**Subgroup._root_.CommGroup.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CommGroup.center_eq_top {G : Type*} [CommGroup G] : center G = ⊤ := by
  rw [eq_top_iff']
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  exact mul_comm y x

@[to_additive]
/-
**Subgroup.center_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：center_eq_top_iff : center G = ⊤ ↔ IsMulCommutative G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem center_eq_top_iff : center G = ⊤ ↔ IsMulCommutative G := by
  simp [eq_top_iff', isMulCommutative_iff, mem_center_iff, eq_comm]

@[to_additive]
/-
**Subgroup.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：center_eq_top [hG : IsMulCommutative G] : center G = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.center_eq_top_iff`：center_eq_top_iff : center G = ⊤ ↔ IsMulComm
utative G
-/
theorem center_eq_top [hG : IsMulCommutative G] : center G = ⊤ :=
    center_eq_top_iff.mpr hG

/-- A group is commutative if the center is the whole group. -/
@[to_additive /-- An additive group is commutative if the center is the whole group. -/,
  instance_reducible]
/-
**Subgroup._root_.Group.commGroupOfCenterEqTop** 是 Mathlib 中的一个定义，位于命名空间 `Subgro
up`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.Group.commGroupOfCenterEqTop (h : center G = ⊤) : CommGroup G :=
  { ‹Group G› with
    mul_comm := by
      rw [eq_top_iff'] at h
      intro x y
      apply Subgroup.mem_center_iff.mp _ x
      exact h y
  }

@[to_additive]
/-
**Subgroup.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Type u_2} [inst_1 : Group H],   Sub
group.center (G × H) = (Subgroup.center G).prod (Subgroup.center H)
参数：G × H；Subgroup.center G；Subgroup.center H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_prod`：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 
: Mul N], Set.center (M × N) = Set.center M ×ˢ Set.center N
-/
protected theorem center_prod {H : Type*} [Group H] : center (G × H) = prod (center G) (center H) :=
  SetLike.coe_injective Set.center_prod

@[to_additive]
/-
**Subgroup.center_pi** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {η : Type u_2} {G : η → Type u_3} [inst : (i : η) → Group (G i)],   Subg
roup.center ((i : η) → G i) = Subgroup.pi Set.univ fun i => Subgroup.center (G i
)
参数：i : η；G i；(i : η) → G i；G i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_pi`：∀ {ι : Type u_2} {A : ι → Type u_3} [inst : (i : ι) → Mul
 (A i)],   Set.center ((i : ι) → A i) = Set.univ.pi fun i => Set.center (A i)
-/
protected theorem center_pi {η : Type*} {G : η → Type*} [Π i, Group (G i)] :
    center (Π i, G i) = pi .univ fun i ↦ center (G i) :=
  SetLike.coe_injective Set.center_pi

variable {H : Subgroup G}

section Normalizer

@[to_additive]
/-
**Subgroup.instNormalCenter** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：instNormalCenter : (center G).Normal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
instance instNormalCenter : (center G).Normal :=
  ⟨fun a ha b ↦ by simpa [mem_center_iff.mp ha b]⟩

@[to_additive]
/-
**Subgroup.center_le_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：center_le_normalizer (s : Set G) : center G <= normalizer s
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem center_le_normalizer (s : Set G) : center G ≤ normalizer s := by
  intro x hx y
  simp [← mem_center_iff.mp hx y]

end Normalizer

end Subgroup

namespace IsConj

variable {M : Type*} [Monoid M]

/-
**IsConj.eq_of_left_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `IsConj`。
形式化陈述：eq_of_left_mem_center {g h : M} (H : IsConj g h) (Hg : g in Set.center M) 
: g = h
参数：H : IsConj g h；Hg : g in Set.center M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_left_inj`：mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b 
= c
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
-/
theorem eq_of_left_mem_center {g h : M} (H : IsConj g h) (Hg : g ∈ Set.center M) : g = h := by
  rcases H with ⟨u, hu⟩; rwa [← u.mul_left_inj, Hg.comm u]
/-
**IsConj.eq_of_right_mem_center** 是 Mathlib 中的一个定理，位于命名空间 `IsConj`。
形式化陈述：eq_of_right_mem_center {g h : M} (H : IsConj g h) (Hh : h in Set.center M)
 : g = h
参数：H : IsConj g h；Hh : h in Set.center M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsConj.eq_of_left_mem_center`：eq_of_left_mem_center {g h : M} (H : IsCon
j g h) (Hg : g in Set.center M) : g = h
· 使用引理 `IsConj.symm`：IsConj.symm (hσ : IsConj φ σ) : IsConj φ σ.symm
-/
theorem eq_of_right_mem_center {g h : M} (H : IsConj g h) (Hh : h ∈ Set.center M) : g = h :=
  (H.symm.eq_of_left_mem_center Hh).symm

end IsConj

namespace ConjClasses

set_option backward.isDefEq.respectTransparency false in
/-
**ConjClasses.mk_bijOn** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：mk_bijOn (G : Type*) [Group G] : Set.BijOn ConjClasses.mk (↑(Subgroup.cent
er G)) (noncenter G)ᶜ
参数：G : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsConj.eq_of_right_mem_center`：eq_of_right_mem_center {g h : M} (H : IsC
onj g h) (Hh : h in Set.center M) : g = h
· 使用定理 `IsConj.eq_of_left_mem_center`：eq_of_left_mem_center {g h : M} (H : IsCon
j g h) (Hg : g in Set.center M) : g = h
· 使用定理 `ConjClasses.mk_eq_mk_iff_isConj`：mk_eq_mk_iff_isConj {a b : α} : ConjCla
sses.mk a = ConjClasses.mk b ↔ IsConj a b
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subgroup.mem_center_iff`：mem_center_iff {z : G} : z in center G ↔ forall
 g, g * z = z * g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `ConjClasses.mem_carrier_iff_mk_eq`：mem_carrier_iff_mk_eq {a : α} {b : Co
njClasses α} : a in carrier b ↔ ConjClasses.mk a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isConj_comm`：isConj_comm {g h : α} : IsConj g h ↔ IsConj h g
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `ConjClasses.mem_carrier_mk`：mem_carrier_mk {a : α} : a in carrier (ConjC
lasses.mk a)
-/
theorem mk_bijOn (G : Type*) [Group G] :
    Set.BijOn ConjClasses.mk (↑(Subgroup.center G)) (noncenter G)ᶜ := by
  refine ⟨fun g hg ↦ ?_, fun x hx y _ H ↦ ?_, ?_⟩
  · simp only [mem_noncenter, Set.compl_def, Set.mem_ofPred, Set.not_nontrivial_iff]
    intro x hx y hy
    simp only [mem_carrier_iff_mk_eq, mk_eq_mk_iff_isConj] at hx hy
    rw [hx.eq_of_right_mem_center hg, hy.eq_of_right_mem_center hg]
  · rw [mk_eq_mk_iff_isConj] at H
    exact H.eq_of_left_mem_center hx
  · rintro ⟨g⟩ hg
    refine ⟨g, ?_, rfl⟩
    simp only [mem_noncenter, Set.compl_def, Set.mem_ofPred, Set.not_nontrivial_iff] at hg
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro h
    rw [← mul_inv_eq_iff_eq_mul]
    refine hg ?_ mem_carrier_mk
    rw [mem_carrier_iff_mk_eq]
    apply mk_eq_mk_iff_isConj.mpr
    rw [isConj_comm, isConj_iff]
    exact ⟨h, rfl⟩

end ConjClasses

