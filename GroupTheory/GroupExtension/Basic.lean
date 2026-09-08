/-
Copyright (c) 2024 Yudai Yamazaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yudai Yamazaki
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.Group

/-!
# Basic lemmas about group extensions

This file gives basic lemmas about group extensions.

For the main definitions, see `Mathlib/GroupTheory/GroupExtension/Defs.lean`.
-/

@[expose] public section

variable {N G : Type*} [Group N] [Group G]

namespace GroupExtension

variable {E : Type*} [Group E] (S : GroupExtension N E G)

/-- The isomorphism `E ⧸ S.rightHom.ker ≃* G` induced by `S.rightHom` -/
@[to_additive /-- The isomorphism `E ⧸ S.rightHom.ker ≃+ G` induced by `S.rightHom` -/]
/-
**GroupExtension.quotientKerRightHomEquivRight** 是 Mathlib 中的一个定义，位于命名空间 `GroupE
xtension`。
形式化陈述：quotientKerRightHomEquivRight : E ⧸ S.rightHom.ker ≃* G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.rightHom_surjective`：∀ {N : Type u_1} {E : Type u_2} {G :
 Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self : Grou
pExtension N E G), Funct…

--- 原说明 ---
The isomorphism `E ⧸ S.rightHom.ker ≃* G` induced by `S.rightHom`
-/
noncomputable def quotientKerRightHomEquivRight : E ⧸ S.rightHom.ker ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective S.rightHom S.rightHom_surjective

/-- The isomorphism `E ⧸ S.inl.range ≃* G` induced by `S.rightHom` -/
@[to_additive /-- The isomorphism `E ⧸ S.inl.range ≃+ G` induced by `S.rightHom` -/]
/-
**GroupExtension.quotientRangeInlEquivRight** 是 Mathlib 中的一个定义，位于命名空间 `GroupExte
nsion`。
形式化陈述：quotientRangeInlEquivRight : E ⧸ S.inl.range ≃* G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.rightHom_surjective`：∀ {N : Type u_1} {E : Type u_2} {G :
 Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self : Grou
pExtension N E G), Funct…
· 使用定理 `GroupExtension.range_inl_eq_ker_rightHom`：∀ {N : Type u_1} {E : Type u_2
} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self 
: GroupExtension N E G), self.…

--- 原说明 ---
The isomorphism `E ⧸ S.inl.range ≃* G` induced by `S.rightHom`
-/
noncomputable def quotientRangeInlEquivRight : E ⧸ S.inl.range ≃* G :=
  QuotientGroup.liftEquiv _ S.rightHom_surjective S.range_inl_eq_ker_rightHom

/-- An arbitrarily chosen section -/
@[to_additive surjInvRightHom /-- An arbitrarily chosen section -/]
/-
**GroupExtension.surjInvRightHom** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension`。
形式化陈述：surjInvRightHom : S.Section where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.rightHom_surjective`：∀ {N : Type u_1} {E : Type u_2} {G :
 Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self : Grou
pExtension N E G), Funct…

--- 原说明 ---
An arbitrarily chosen section
-/
noncomputable def surjInvRightHom : S.Section where
  toFun := Function.surjInv S.rightHom_surjective
  rightInverse_rightHom := Function.surjInv_eq S.rightHom_surjective

namespace Section

variable {S}
variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G} (σ σ' : S.Section) (g g₁ g₂ : G)
  (equiv : S.Equiv S')

@[to_additive]
/-
**GroupExtension.Section.mul_inv_mem_range_inl** 是 Mathlib 中的一个定理，位于命名空间 `GroupE
xtension.Section`。
形式化陈述：mul_inv_mem_range_inl : σ g * (σ' g)⁻¹ in S.inl.range
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupExtension.range_inl_eq_ker_rightHom`：∀ {N : Type u_1} {E : Type u_2
} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self 
: GroupExtension N E G), self.…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `GroupExtension.Section.rightHom_section`：rightHom_section (g : G) : S.ri
ghtHom (σ g) = g
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_inv_mem_range_inl : σ g * (σ' g)⁻¹ ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]
/-
**GroupExtension.Section.inv_mul_mem_range_inl** 是 Mathlib 中的一个定理，位于命名空间 `GroupE
xtension.Section`。
形式化陈述：inv_mul_mem_range_inl : (σ g)⁻¹ * σ' g in S.inl.range
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupExtension.range_inl_eq_ker_rightHom`：∀ {N : Type u_1} {E : Type u_2
} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self 
: GroupExtension N E G), self.…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `GroupExtension.Section.rightHom_section`：rightHom_section (g : G) : S.ri
ghtHom (σ g) = g
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_mul_mem_range_inl : (σ g)⁻¹ * σ' g ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    inv_mul_cancel]

@[to_additive]
/-
**GroupExtension.Section.exists_eq_inl_mul** 是 Mathlib 中的一个定理，位于命名空间 `GroupExten
sion.Section`。
形式化陈述：exists_eq_inl_mul : exists n : N, σ g = S.inl n * σ' g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.Section.mul_inv_mem_range_inl`：mul_inv_mem_range_inl : σ 
g * (σ' g)⁻¹ in S.inl.range
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
theorem exists_eq_inl_mul : ∃ n : N, σ g = S.inl n * σ' g := by
  obtain ⟨n, hn⟩ := mul_inv_mem_range_inl σ σ' g
  exact ⟨n, by rw [hn, inv_mul_cancel_right]⟩

@[to_additive]
/-
**GroupExtension.Section.exists_eq_mul_inl** 是 Mathlib 中的一个定理，位于命名空间 `GroupExten
sion.Section`。
形式化陈述：exists_eq_mul_inl : exists n : N, σ g = σ' g * S.inl n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.Section.inv_mul_mem_range_inl`：inv_mul_mem_range_inl : (σ
 g)⁻¹ * σ' g in S.inl.range
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem exists_eq_mul_inl : ∃ n : N, σ g = σ' g * S.inl n := by
  obtain ⟨n, hn⟩ := inv_mul_mem_range_inl σ' σ g
  exact ⟨n, by rw [hn, mul_inv_cancel_left]⟩

@[to_additive]
/-
**GroupExtension.Section.mul_mul_mul_inv_mem_range_inl** 是 Mathlib 中的一个定理，位于命名空间
 `GroupExtension.Section`。
形式化陈述：mul_mul_mul_inv_mem_range_inl : σ g₁ * σ g₂ * (σ (g₁ * g₂))⁻¹ in S.inl.ran
ge
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupExtension.range_inl_eq_ker_rightHom`：∀ {N : Type u_1} {E : Type u_2
} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self 
: GroupExtension N E G), self.…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `GroupExtension.Section.rightHom_section`：rightHom_section (g : G) : S.ri
ghtHom (σ g) = g
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_mul_mul_inv_mem_range_inl : σ g₁ * σ g₂ * (σ (g₁ * g₂))⁻¹ ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]
/-
**GroupExtension.Section.mul_inv_mul_mul_mem_range_inl** 是 Mathlib 中的一个定理，位于命名空间
 `GroupExtension.Section`。
形式化陈述：mul_inv_mul_mul_mem_range_inl : (σ (g₁ * g₂))⁻¹ * σ g₁ * σ g₂ in S.inl.ran
ge
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupExtension.range_inl_eq_ker_rightHom`：∀ {N : Type u_1} {E : Type u_2
} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self 
: GroupExtension N E G), self.…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `GroupExtension.Section.rightHom_section`：rightHom_section (g : G) : S.ri
ghtHom (σ g) = g
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_inv_mul_mul_mem_range_inl : (σ (g₁ * g₂))⁻¹ * σ g₁ * σ g₂ ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_assoc, inv_mul_cancel]

@[to_additive]
/-
**GroupExtension.Section.exists_mul_eq_inl_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Gr
oupExtension.Section`。
形式化陈述：exists_mul_eq_inl_mul_mul : exists n : N, σ (g₁ * g₂) = S.inl n * σ g₁ * σ
 g₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.Section.mul_mul_mul_inv_mem_range_inl`：mul_mul_mul_inv_me
m_range_inl : σ g₁ * σ g₂ * (σ (g₁ * g₂))⁻¹ in S.inl.range
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
-/
theorem exists_mul_eq_inl_mul_mul : ∃ n : N, σ (g₁ * g₂) = S.inl n * σ g₁ * σ g₂ := by
  obtain ⟨n, hn⟩ := mul_mul_mul_inv_mem_range_inl σ g₁ g₂
  use n⁻¹
  rw [mul_assoc, map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq, hn]

@[to_additive]
/-
**GroupExtension.Section.exists_mul_eq_mul_mul_inl** 是 Mathlib 中的一个定理，位于命名空间 `Gr
oupExtension.Section`。
形式化陈述：exists_mul_eq_mul_mul_inl : exists n : N, σ (g₁ * g₂) = σ g₁ * σ g₂ * S.in
l n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.Section.mul_inv_mul_mul_mem_range_inl`：mul_inv_mul_mul_me
m_range_inl : (σ (g₁ * g₂))⁻¹ * σ g₁ * σ g₂ in S.inl.range
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem exists_mul_eq_mul_mul_inl : ∃ n : N, σ (g₁ * g₂) = σ g₁ * σ g₂ * S.inl n := by
  obtain ⟨n, hn⟩ := mul_inv_mul_mul_mem_range_inl σ g₁ g₂
  use n⁻¹
  rw [map_inv, eq_mul_inv_iff_mul_eq, ← eq_inv_mul_iff_mul_eq, ← mul_assoc, hn]

initialize_simps_projections AddGroupExtension.Section (toFun → apply)
initialize_simps_projections Section (toFun → apply)

/-- The composition of an isomorphism between equivalent group extensions and a section -/
@[to_additive (attr := simps!)
/-- The composition of an isomorphism between equivalent additive group extensions and a section -/]
/-
**GroupExtension.Section.equivComp** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension.Sec
tion`。
形式化陈述：equivComp : S'.Section where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivComp : S'.Section where
  toFun := equiv ∘ σ
  rightInverse_rightHom g := by
    rw [Function.comp_apply, equiv.rightHom_map, rightHom_section]

end Section

namespace Equiv

variable {S}
variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G}

/-- An equivalence of group extensions from a homomorphism making a commuting diagram. Such a
homomorphism is necessarily an isomorphism. -/
@[to_additive
/-- An equivalence of additive group extensions from a homomorphism making a commuting diagram.
Such a homomorphism is necessarily an isomorphism. -/]
/-
**GroupExtension.Equiv.ofMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension.Equ
iv`。
形式化陈述：ofMonoidHom (f : E ->* E') (comp_inl : f.comp S.inl = S'.inl) (rightHom_co
mp : S'.rightHom.comp f = S.rightHom) : S.Equiv S' where __
参数：f : E ->* E'；comp_inl : f.comp S.inl = S'.inl；rightHom_comp : S'.rightHom.com
p f = S.rightHom。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.rightHom_surjective`：∀ {N : Type u_1} {E : Type u_2} {G :
 Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self : Grou
pExtension N E G), Funct…
-/
noncomputable def ofMonoidHom (f : E →* E') (comp_inl : f.comp S.inl = S'.inl)
    (rightHom_comp : S'.rightHom.comp f = S.rightHom) : S.Equiv S' where
  __ := f
  invFun e' :=
    let e := Function.surjInv S.rightHom_surjective (S'.rightHom e')
    e * S.inl (Function.invFun S'.inl ((f e)⁻¹ * e'))
  left_inv e := by
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, ← map_inv, ← map_mul]
    obtain ⟨n, hn⟩ :
        (Function.surjInv S.rightHom_surjective (S'.rightHom (f e)))⁻¹ * e ∈ S.inl.range := by
      rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply,
        rightHom_comp]
      simpa only [Function.surjInv_eq] using inv_mul_cancel (S.rightHom e)
    rw [← eq_inv_mul_iff_mul_eq, ← hn, ← MonoidHom.comp_apply, comp_inl,
      Function.leftInverse_invFun S'.inl_injective]
  right_inv e' := by
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, map_mul]
    rw [← eq_inv_mul_iff_mul_eq, ← MonoidHom.comp_apply, comp_inl]
    apply Function.invFun_eq
    rw [← MonoidHom.mem_range, S'.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv,
      ← MonoidHom.comp_apply, rightHom_comp]
    simpa only [Function.surjInv_eq] using inv_mul_cancel (S'.rightHom e')
  inl_comm := congrArg DFunLike.coe comp_inl
  rightHom_comm := congrArg DFunLike.coe rightHom_comp

end Equiv

namespace Splitting

variable {S}
variable (s : S.Splitting)

/-- `G` acts on `N` by conjugation. -/
/-
**GroupExtension.Splitting.conjAct** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension.Spl
itting`。
形式化陈述：conjAct : G ->* MulAut N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.Splitting.instMonoidHomClass`：∀ {N : Type u_1} {E : Type 
u_2} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (S 
: GroupExtension N E G), MonoidHo…

--- 原说明 ---
`G` acts on `N` by conjugation.
-/
noncomputable def conjAct : G →* MulAut N := S.conjAct.comp s

set_option backward.isDefEq.respectTransparency false in
/-- A split group extension is equivalent to the extension associated to a semidirect product. -/
/-
**GroupExtension.Splitting.semidirectProductToGroupExtensionEquiv** 是 Mathlib 中的
一个定义，位于命名空间 `GroupExtension.Splitting`。
形式化陈述：semidirectProductToGroupExtensionEquiv : (SemidirectProduct.toGroupExtensi
on s.conjAct).Equiv S where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A split group extension is equivalent to the extension associated to a semidirec
t product.
-/
noncomputable def semidirectProductToGroupExtensionEquiv :
    (SemidirectProduct.toGroupExtension s.conjAct).Equiv S where
  toFun := fun ⟨n, g⟩ ↦ S.inl n * s g
  invFun := fun e ↦ ⟨Function.invFun S.inl (e * (s (S.rightHom e))⁻¹), S.rightHom e⟩
  left_inv := fun ⟨n, g⟩ ↦ by
    simp only [map_mul, rightHom_inl, rightHom_splitting, one_mul, mul_inv_cancel_right,
      Function.leftInverse_invFun S.inl_injective n]
  right_inv := fun e ↦ by
    simp only [← eq_mul_inv_iff_mul_eq]
    apply Function.invFun_eq
    rw [← MonoidHom.mem_range, S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv,
      rightHom_splitting, mul_inv_cancel]
  map_mul' := fun ⟨n₁, g₁⟩ ⟨n₂, g₂⟩ ↦ by
    simp only [conjAct, MonoidHom.comp_apply, map_mul, inl_conjAct_comm, MonoidHom.coe_coe]
    group
  inl_comm := by
    ext n
    simp only [SemidirectProduct.toGroupExtension, Function.comp_apply, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]
  rightHom_comm := by
    ext ⟨n, g⟩
    simp only [SemidirectProduct.toGroupExtension, Function.comp_apply, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, map_mul, rightHom_inl, one_mul, rightHom_splitting,
      SemidirectProduct.rightHom_eq_right]

/-- The group associated to a split extension is isomorphic to a semidirect product. -/
/-
**GroupExtension.Splitting.semidirectProductMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
GroupExtension.Splitting`。
形式化陈述：semidirectProductMulEquiv : N ⋊[s.conjAct] G ≃* E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group associated to a split extension is isomorphic to a semidirect product.
-/
noncomputable def semidirectProductMulEquiv : N ⋊[s.conjAct] G ≃* E :=
  s.semidirectProductToGroupExtensionEquiv.toMulEquiv

end Splitting

namespace IsConj

/-- `N`-conjugacy is reflexive. -/
@[to_additive /-- `N`-conjugacy is reflexive. -/]
/-
**GroupExtension.IsConj.refl** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension.IsConj`。
形式化陈述：refl (s : S.Splitting) : S.IsConj s s
参数：s : S.Splitting。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`N`-conjugacy is reflexive.
-/
theorem refl (s : S.Splitting) : S.IsConj s s :=
  ⟨1, by simp only [map_one, inv_one, one_mul, mul_one]⟩

/-- `N`-conjugacy is symmetric. -/
@[to_additive /-- `N`-conjugacy is symmetric. -/]
/-
**GroupExtension.IsConj.symm** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension.IsConj`。
形式化陈述：symm {s₁ s₂ : S.Splitting} (h : S.IsConj s₁ s₂) : S.IsConj s₂ s₁
参数：h : S.IsConj s₁ s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.mul_neg`：∀ (a b : ℤ), a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `Mathlib.Tactic.Group._zpow_trick_one'`：_zpow_trick_one' {G : Type*} [Gro
up G] (a b : G) (n : Int) : a * b ^ n * b = a * b ^ (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`N`-conjugacy is symmetric.
-/
theorem symm {s₁ s₂ : S.Splitting} (h : S.IsConj s₁ s₂) : S.IsConj s₂ s₁ := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n⁻¹, by simp only [hn, map_inv]; group⟩

/-- `N`-conjugacy is transitive. -/
@[to_additive /-- `N`-conjugacy is transitive. -/]
/-
**GroupExtension.IsConj.trans** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension.IsConj`。
形式化陈述：trans {s₁ s₂ s₃ : S.Splitting} (h₁ : S.IsConj s₁ s₂) (h₂ : S.IsConj s₂ s₃)
 : S.IsConj s₁ s₃
参数：h₁ : S.IsConj s₁ s₂；h₂ : S.IsConj s₂ s₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `mul_zpow_neg_one`：mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : Int) = b 
^ (-1 : Int) * a ^ (-1 : Int)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`N`-conjugacy is transitive.
-/
theorem trans {s₁ s₂ s₃ : S.Splitting} (h₁ : S.IsConj s₁ s₂) (h₂ : S.IsConj s₂ s₃) :
    S.IsConj s₁ s₃ := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  exact ⟨n₁ * n₂, by simp only [hn₁, hn₂, map_mul]; group⟩

/-- The setoid of splittings with `N`-conjugacy -/
@[to_additive /-- The setoid of splittings with `N`-conjugacy -/]
/-
**GroupExtension.IsConj.setoid** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension.IsConj`
。
形式化陈述：setoid : Setoid S.Splitting where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid of splittings with `N`-conjugacy
-/
def setoid : Setoid S.Splitting where
  r := S.IsConj
  iseqv :=
  { refl := refl S
    symm := symm S
    trans := trans S }

end IsConj

/-- The `N`-conjugacy classes of splittings -/
@[to_additive /-- The `N`-conjugacy classes of splittings -/]
/-
**GroupExtension.ConjClasses** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension`。
形式化陈述：ConjClasses
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `N`-conjugacy classes of splittings
-/
def ConjClasses := Quotient <| IsConj.setoid S

end GroupExtension

namespace SemidirectProduct

variable {φ : G →* MulAut N} (s : (toGroupExtension φ).Splitting)

/-
**SemidirectProduct.right_splitting** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectProduct
`。
形式化陈述：right_splitting (g : G) : (s g).right = g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemidirectProduct.rightHom_eq_right`：rightHom_eq_right : (rightHom : N ⋊
[φ] G -> G) = right
· 使用定理 `SemidirectProduct.toGroupExtension_rightHom`：toGroupExtension_rightHom :
 (toGroupExtension φ).rightHom = SemidirectProduct.rightHom
· 使用定理 `GroupExtension.Splitting.rightHom_splitting`：rightHom_splitting (g : G) 
: S.rightHom (s g) = g
-/
theorem right_splitting (g : G) : (s g).right = g := by
  rw [← rightHom_eq_right, ← toGroupExtension_rightHom, s.rightHom_splitting]

end SemidirectProduct

