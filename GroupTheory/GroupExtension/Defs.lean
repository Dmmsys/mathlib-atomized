/-
Copyright (c) 2024 Yudai Yamazaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yudai Yamazaki
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Group Extensions

This file defines extensions of multiplicative and additive groups and their associated structures
such as splittings and equivalences.

## Main definitions

- `(Add?)GroupExtension N E G`: structure for extensions of `G` by `N` as short exact sequences
  `1 → N → E → G → 1` (`0 → N → E → G → 0` for additive groups)
- `(Add?)GroupExtension.Equiv S S'`: structure for equivalences of two group extensions `S` and `S'`
  as specific homomorphisms `E → E'` such that each diagram below is commutative

```text
For multiplicative groups:
      ↗ E  ↘
1 → N   ↓    G → 1
      ↘ E' ↗

For additive groups:
      ↗ E  ↘
0 → N   ↓    G → 0
      ↘ E' ↗
```

- `(Add?)GroupExtension.Section S`: structure for right inverses to `rightHom` of a group extension
  `S` of `G` by `N`
- `(Add?)GroupExtension.Splitting S`: structure for section homomorphisms of a group extension `S`
  of `G` by `N`
- `SemidirectProduct.toGroupExtension φ`: the multiplicative group extension associated to the
  semidirect product coming from `φ : G →* MulAut N`, `1 → N → N ⋊[φ] G → G → 1`

## TODO

If `N` is abelian,

- there is a bijection between `N`-conjugacy classes of
  `(SemidirectProduct.toGroupExtension φ).Splitting` and `groupCohomology.H1`
  (which will be available in the planned file `Mathlib/GroupTheory/GroupExtension/Abelian.lean` to
  be added in a later PR).
- there is a bijection between equivalence classes of group extensions and `groupCohomology.H2`
  (which is also stated as a TODO in `Mathlib/RepresentationTheory/GroupCohomology/LowDegree.lean`).
-/

@[expose] public section

variable (N E G : Type*)

/-- `AddGroupExtension N E G` is a short exact sequence of additive groups `0 → N → E → G → 0`. -/
/-
**AddGroupExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(N : Type u_1) →   (E : Type u_2) → (G : Type u_3) → [AddGroup N] → [AddGr
oup E] → [AddGroup G] → Type (max (max u_1 u_2) u_3)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddGroupExtension N E G` is a short exact sequence of additive groups `0 → N → 
E → G → 0`.
-/
structure AddGroupExtension [AddGroup N] [AddGroup E] [AddGroup G] where
  /-- The inclusion homomorphism `N →+ E` -/
  inl : N →+ E
  /-- The projection homomorphism `E →+ G` -/
  rightHom : E →+ G
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom

/-- `GroupExtension N E G` is a short exact sequence of groups `1 → N → E → G → 1`. -/
@[to_additive]
/-
**GroupExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(N : Type u_1) → (E : Type u_2) → (G : Type u_3) → [Group N] → [Group E] →
 [Group G] → Type (max (max u_1 u_2) u_3)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`GroupExtension N E G` is a short exact sequence of groups `1 → N → E → G → 1`.
-/
structure GroupExtension [Group N] [Group E] [Group G] where
  /-- The inclusion homomorphism `N →* E` -/
  inl : N →* E
  /-- The projection homomorphism `E →* G` -/
  rightHom : E →* G
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom

variable {N E G}

namespace AddGroupExtension

variable [AddGroup N] [AddGroup E] [AddGroup G] (S : AddGroupExtension N E G)

/-- `AddGroupExtension`s are equivalent iff there is an isomorphism making a commuting diagram.
  Use `AddGroupExtension.Equiv.ofMonoidHom` in `Mathlib/GroupTheory/GroupExtension/Basic.lean` to
  construct an equivalence without providing the inverse map. -/
/-
**AddGroupExtension.Equiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddGroupExtension`。
形式化陈述：{N : Type u_1} →   {E : Type u_2} →     {G : Type u_3} →       [inst : Add
Group N] →         [inst_1 : AddGroup E] →           [inst_2 : AddGroup G] →    
         AddGroupExtension N E G →               {E' : Type u_4} → [inst_3 : Add
Group E'] → AddGroupExtension N E' G → Type (max u_2 u_4)
参数：max u_2 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddGroupExtension`s are equivalent iff there is an isomorphism making a commuti
ng diagram.
  Use `AddGroupExtension.Equiv.ofMonoidHom` in `Mathlib/GroupTheory/GroupExtensi
on/Basic.lean` to
  construct an equivalence without providing the inverse map.
-/
structure Equiv {E' : Type*} [AddGroup E'] (S' : AddGroupExtension N E' G) extends E ≃+ E' where
  /-- The left-hand side of the diagram commutes. -/
  inl_comm : toAddEquiv ∘ S.inl = S'.inl
  /-- The right-hand side of the diagram commutes. -/
  rightHom_comm : S'.rightHom ∘ toAddEquiv = S.rightHom

/-- `Section` of an additive group extension is a right inverse to `S.rightHom`. -/
/-
**AddGroupExtension.Section** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddGroupExtension`。
形式化陈述：{N : Type u_1} →   {E : Type u_2} →     {G : Type u_3} →       [inst : Add
Group N] → [inst_1 : AddGroup E] → [inst_2 : AddGroup G] → AddGroupExtension N E
 G → Type (max u_2 u_3)
参数：max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Section` of an additive group extension is a right inverse to `S.rightHom`.
-/
structure Section where
  /-- The underlying function -/
  toFun : G → E
  /-- `Section` is a right inverse to `S.rightHom` -/
  rightInverse_rightHom : Function.RightInverse toFun S.rightHom

/-- `Splitting` of an additive group extension is a section homomorphism. -/
/-
**AddGroupExtension.Splitting** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddGroupExtension`。
形式化陈述：{N : Type u_1} →   {E : Type u_2} →     {G : Type u_3} →       [inst : Add
Group N] → [inst_1 : AddGroup E] → [inst_2 : AddGroup G] → AddGroupExtension N E
 G → Type (max u_2 u_3)
参数：max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Splitting` of an additive group extension is a section homomorphism.
-/
structure Splitting extends G →+ E, S.Section

/-- A splitting of an additive group extension as a (set-theoretic) section. -/
add_decl_doc Splitting.toSection

end AddGroupExtension

namespace GroupExtension

variable [Group N] [Group E] [Group G] (S : GroupExtension N E G)

/-- The range of the inclusion map is a normal subgroup. -/
@[to_additive /-- The range of the inclusion map is a normal additive subgroup. -/]
/-
**GroupExtension.normal_inl_range** 是 Mathlib 中的一个实例，位于命名空间 `GroupExtension`。
形式化陈述：normal_inl_range : S.inl.range.Normal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GroupExtension.range_inl_eq_ker_rightHom`：∀ {N : Type u_1} {E : Type u_2
} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self 
: GroupExtension N E G), self.…

--- 原说明 ---
The range of the inclusion map is a normal subgroup.
-/
instance normal_inl_range : S.inl.range.Normal :=
  S.range_inl_eq_ker_rightHom ▸ S.rightHom.normal_ker

@[to_additive (attr := simp)]
/-
**GroupExtension.rightHom_inl** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension`。
形式化陈述：rightHom_inl (n : N) : S.rightHom (S.inl n) = 1
参数：n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `GroupExtension.range_inl_eq_ker_rightHom`：∀ {N : Type u_1} {E : Type u_2
} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self 
: GroupExtension N E G), self.…
· 使用定理 `MonoidHom.mem_range`：mem_range {f : G ->* N} {y : N} : y in f.range ↔ ex
ists x, f x = y
· 使用定理 `exists_apply_eq_apply`：∀ {α : Sort u_2} {β : Sort u_1} (f : α → β) (a' :
 α), ∃ a, f a = f a'
-/
theorem rightHom_inl (n : N) : S.rightHom (S.inl n) = 1 := by
  rw [← MonoidHom.mem_ker, ← S.range_inl_eq_ker_rightHom, MonoidHom.mem_range]
  exact exists_apply_eq_apply S.inl n

@[to_additive (attr := simp)]
/-
**GroupExtension.rightHom_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension`。
形式化陈述：rightHom_comp_inl : S.rightHom.comp S.inl = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.one_apply`：MonoidHom.one_apply [MulOne M] [MulOneClass N] (x :
 M) : (1 : M ->* N) x = 1
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
· 使用定理 `GroupExtension.rightHom_inl`：rightHom_inl (n : N) : S.rightHom (S.inl n)
 = 1
-/
theorem rightHom_comp_inl : S.rightHom.comp S.inl = 1 := by
  ext n
  rw [MonoidHom.one_apply, MonoidHom.comp_apply]
  exact S.rightHom_inl n

/-- `E` acts on `N` by conjugation. -/
/-
**GroupExtension.conjAct** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension`。
形式化陈述：conjAct : E ->* MulAut N where toFun e
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.inl_injective`：∀ {N : Type u_1} {E : Type u_2} {G : Type 
u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self : GroupExten
sion N E G), Funct…

--- 原说明 ---
`E` acts on `N` by conjugation.
-/
noncomputable def conjAct : E →* MulAut N where
  toFun e := (MonoidHom.ofInjective S.inl_injective).trans <|
    (MulAut.conjNormal e).trans (MonoidHom.ofInjective S.inl_injective).symm
  map_one' := by
    ext _
    simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' _ _ := by
    ext _
    simp only [map_mul, MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.apply_symm_apply]

/-- The inclusion and a conjugation commute. -/
/-
**GroupExtension.inl_conjAct_comm** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension`。
形式化陈述：inl_conjAct_comm {e : E} {n : N} : S.inl (S.conjAct e n) = e * S.inl n * e
⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.apply_ofInjective_symm`：apply_ofInjective_symm {f : G ->* N} (
hf : Function.Injective f) (x : f.range) : f ((ofInjective hf).symm x) = x
· 使用定理 `GroupExtension.inl_injective`：∀ {N : Type u_1} {E : Type u_2} {G : Type 
u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (self : GroupExten
sion N E G), Funct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inclusion and a conjugation commute.
-/
theorem inl_conjAct_comm {e : E} {n : N} : S.inl (S.conjAct e n) = e * S.inl n * e⁻¹ := by
  simp only [conjAct, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

/-- `GroupExtension`s are equivalent iff there is an isomorphism making a commuting diagram.
  Use `GroupExtension.Equiv.ofMonoidHom` in `Mathlib/GroupTheory/GroupExtension/Basic.lean` to
  construct an equivalence without providing the inverse map. -/
@[to_additive]
/-
**GroupExtension.Equiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `GroupExtension`。
形式化陈述：{N : Type u_1} →   {E : Type u_2} →     {G : Type u_3} →       [inst : Gro
up N] →         [inst_1 : Group E] →           [inst_2 : Group G] →             
GroupExtension N E G → {E' : Type u_4} → [inst_3 : Group E'] → GroupExtension N 
E' G → Type (max u_2 u_4)
参数：max u_2 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`GroupExtension`s are equivalent iff there is an isomorphism making a commuting 
diagram.
  Use `GroupExtension.Equiv.ofMonoidHom` in `Mathlib/GroupTheory/GroupExtension/
Basic.lean` to
  construct an equivalence without providing the inverse map.
-/
structure Equiv {E' : Type*} [Group E'] (S' : GroupExtension N E' G) extends E ≃* E' where
  /-- The left-hand side of the diagram commutes. -/
  inl_comm : toMulEquiv ∘ S.inl = S'.inl
  /-- The right-hand side of the diagram commutes. -/
  rightHom_comm : S'.rightHom ∘ toMulEquiv = S.rightHom

namespace Equiv

variable {S}
variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G}

@[to_additive]
/-
**GroupExtension.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `GroupExtension.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (S.Equiv S') E E' where
  coe equiv := equiv.toMulEquiv
  inv equiv := equiv.toMulEquiv.symm
  left_inv equiv := equiv.left_inv
  right_inv equiv := equiv.right_inv
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ h _ ↦ by
    congr
    rw [MulEquiv.ext_iff]
    exact congrFun h

@[to_additive]
/-
**GroupExtension.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `GroupExtension.Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulEquivClass (S.Equiv S') E E' where
  map_mul equiv := equiv.map_mul'

variable (equiv : S.Equiv S')

@[to_additive (attr := simp)]
/-
**GroupExtension.Equiv.toMulEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtensi
on.Equiv`。
形式化陈述：toMulEquiv_eq_coe : equiv.toMulEquiv = equiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMulEquiv_eq_coe : equiv.toMulEquiv = equiv := rfl

@[to_additive (attr := simp)]
/-
**GroupExtension.Equiv.coe_toMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension.
Equiv`。
形式化陈述：coe_toMulEquiv : ⇑(equiv : E ≃* E') = equiv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.Equiv.instMulEquivClass`：∀ {N : Type u_1} {E : Type u_2} 
{G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   {S : Gro
upExtension N E G} {E' : Typ…
-/
theorem coe_toMulEquiv : ⇑(equiv : E ≃* E') = equiv := rfl

@[to_additive (attr := simp)]
/-
**GroupExtension.Equiv.map_inl** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension.Equiv`。
形式化陈述：map_inl (n : N) : equiv (S.inl n) = S'.inl n
参数：n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `GroupExtension.Equiv.inl_comm`：∀ {N : Type u_1} {E : Type u_2} {G : Type
 u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   {S : GroupExtensi
on N E G} {E' : Typ…
-/
theorem map_inl (n : N) : equiv (S.inl n) = S'.inl n := congrFun equiv.inl_comm n

@[to_additive (attr := simp)]
/-
**GroupExtension.Equiv.rightHom_map** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension.Eq
uiv`。
形式化陈述：rightHom_map (e : E) : S'.rightHom (equiv e) = S.rightHom e
参数：e : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `GroupExtension.Equiv.rightHom_comm`：∀ {N : Type u_1} {E : Type u_2} {G :
 Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   {S : GroupEx
tension N E G} {E' : Typ…
-/
theorem rightHom_map (e : E) : S'.rightHom (equiv e) = S.rightHom e :=
  congrFun equiv.rightHom_comm e

/-- The inverse of an equivalence of group extensions is an equivalence. -/
@[to_additive /-- The inverse of an equivalence of additive group extensions is an equivalence. -/]
/-
**GroupExtension.Equiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension.Equiv`。
形式化陈述：symm : S'.Equiv S where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of an equivalence of group extensions is an equivalence.
-/
def symm : S'.Equiv S where
  __ := equiv.toMulEquiv.symm
  inl_comm := by rw [MulEquiv.symm_comp_eq, ← equiv.inl_comm]
  rightHom_comm := by rw [MulEquiv.comp_symm_eq, ← equiv.rightHom_comm]

/-- See Note [custom simps projection]. -/
@[to_additive /-- See Note [custom simps projection]. -/]
/-
**GroupExtension.Equiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtensio
n.Equiv.Simps`。
形式化陈述：{N : Type u_1} →   {E : Type u_2} →     {G : Type u_3} →       [inst : Gro
up N] →         [inst_1 : Group E] →           [inst_2 : Group G] →             
{S : GroupExtension N E G} →               {E' : Type u_4} → [inst_3 : Group E']
 → {S' : GroupExtension N E' G} → S.Equiv S' → E' → E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.symm_apply : E' → E := equiv.symm

@[to_additive (attr := simp)]
/-
**GroupExtension.Equiv.coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension.Equiv`
。
形式化陈述：coe_symm : (equiv : E ≃* E').symm = equiv.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.Equiv.instMulEquivClass`：∀ {N : Type u_1} {E : Type u_2} 
{G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   {S : Gro
upExtension N E G} {E' : Typ…
-/
theorem coe_symm : (equiv : E ≃* E').symm = equiv.symm := rfl

initialize_simps_projections AddGroupExtension.Equiv (toFun → apply, invFun → symm_apply)
initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)

attribute [simps! symm_apply] AddGroupExtension.Equiv.symm
attribute [simps! symm_apply] symm

/-- The composition of monoid isomorphisms associated to equivalences of group extensions gives
another equivalence. -/
@[to_additive (attr := simps!)
/-- The composition of monoid isomorphisms associated to equivalences of additive group
extensions gives another equivalence. -/]
/-
**GroupExtension.Equiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension.Equiv`。
形式化陈述：trans {E'' : Type*} [Group E''] {S'' : GroupExtension N E'' G} (equiv' : S
'.Equiv S'') : S.Equiv S'' where __
参数：equiv' : S'.Equiv S''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def trans {E'' : Type*} [Group E''] {S'' : GroupExtension N E'' G} (equiv' : S'.Equiv S'') :
    S.Equiv S'' where
  __ := equiv.toMulEquiv.trans equiv'.toMulEquiv
  inl_comm := by rw [MulEquiv.coe_trans, Function.comp_assoc, equiv.inl_comm, equiv'.inl_comm]
  rightHom_comm := by
    rw [MulEquiv.coe_trans, ← Function.comp_assoc, equiv'.rightHom_comm, equiv.rightHom_comm]

variable (S)
/-- A group extension is equivalent to itself. -/
@[to_additive (attr := simps!) /-- An additive group extension is equivalent to itself. -/]
/-
**GroupExtension.Equiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension.Equiv`。
形式化陈述：refl : S.Equiv S where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group extension is equivalent to itself.
-/
def refl : S.Equiv S where
  __ := MulEquiv.refl E
  inl_comm := rfl
  rightHom_comm := rfl

end Equiv

/-- `Section` of a group extension is a right inverse to `S.rightHom`. -/
@[to_additive]
/-
**GroupExtension.Section** 是 Mathlib 中的一个归纳类型，位于命名空间 `GroupExtension`。
形式化陈述：{N : Type u_1} →   {E : Type u_2} →     {G : Type u_3} →       [inst : Gro
up N] → [inst_1 : Group E] → [inst_2 : Group G] → GroupExtension N E G → Type (m
ax u_2 u_3)
参数：max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Section` of a group extension is a right inverse to `S.rightHom`.
-/
structure Section where
  /-- The underlying function -/
  toFun : G → E
  /-- `Section` is a right inverse to `S.rightHom` -/
  rightInverse_rightHom : Function.RightInverse toFun S.rightHom

namespace Section

@[to_additive]
/-
**GroupExtension.Section.** 是 Mathlib 中的一个实例，位于命名空间 `GroupExtension.Section`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike S.Section G E where
  coe := toFun
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ _ ↦ by congr

variable {S}

@[to_additive (attr := simp)]
/-
**GroupExtension.Section.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension.Sectio
n`。
形式化陈述：coe_mk (σ : G -> E) (hσ : Function.RightInverse σ S.rightHom) : (mk σ hσ :
 G -> E) = σ
参数：σ : G -> E；hσ : Function.RightInverse σ S.rightHom。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (σ : G → E) (hσ : Function.RightInverse σ S.rightHom) : (mk σ hσ : G → E) = σ := rfl

variable (σ : S.Section)

@[to_additive (attr := simp)]
/-
**GroupExtension.Section.rightHom_section** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtens
ion.Section`。
形式化陈述：rightHom_section (g : G) : S.rightHom (σ g) = g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.Section.rightInverse_rightHom`：∀ {N : Type u_1} {E : Type
 u_2} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   {S
 : GroupExtension N E G} (self : S…
-/
theorem rightHom_section (g : G) : S.rightHom (σ g) = g := σ.rightInverse_rightHom g

@[to_additive (attr := simp)]
/-
**GroupExtension.Section.rightHom_comp_section** 是 Mathlib 中的一个定理，位于命名空间 `GroupE
xtension.Section`。
形式化陈述：rightHom_comp_section : S.rightHom ∘ σ = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse f g → g ∘ f = id
· 使用定理 `GroupExtension.Section.rightInverse_rightHom`：∀ {N : Type u_1} {E : Type
 u_2} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   {S
 : GroupExtension N E G} (self : S…
-/
theorem rightHom_comp_section : S.rightHom ∘ σ = id := σ.rightInverse_rightHom.comp_eq_id

end Section

/-- `Splitting` of a group extension is a section homomorphism. -/
@[to_additive]
/-
**GroupExtension.Splitting** 是 Mathlib 中的一个归纳类型，位于命名空间 `GroupExtension`。
形式化陈述：{N : Type u_1} →   {E : Type u_2} →     {G : Type u_3} →       [inst : Gro
up N] → [inst_1 : Group E] → [inst_2 : Group G] → GroupExtension N E G → Type (m
ax u_2 u_3)
参数：max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Splitting` of a group extension is a section homomorphism.
-/
structure Splitting extends G →* E, S.Section

/-- A splitting of a group extension as a (set-theoretic) section. -/
add_decl_doc Splitting.toSection

namespace Splitting

@[to_additive]
/-
**GroupExtension.Splitting.** 是 Mathlib 中的一个实例，位于命名空间 `GroupExtension.Splitting`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike S.Splitting G E where
  coe s := s.toFun
  coe_injective := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

@[to_additive]
/-
**GroupExtension.Splitting.** 是 Mathlib 中的一个实例，位于命名空间 `GroupExtension.Splitting`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidHomClass S.Splitting G E where
  map_mul s := s.map_mul'
  map_one s := s.map_one'

variable {S}

@[to_additive (attr := simp)]
/-
**GroupExtension.Splitting.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `GroupExtension.Spli
tting`。
形式化陈述：coe_mk (s : G ->* E) (hs : Function.RightInverse s S.rightHom) : (mk s hs 
: G -> E) = s
参数：s : G ->* E；hs : Function.RightInverse s S.rightHom。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : G →* E) (hs : Function.RightInverse s S.rightHom) : (mk s hs : G → E) = s := rfl

@[to_additive (attr := simp)]
/-
**GroupExtension.Splitting.coe_monoidHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `GroupExte
nsion.Splitting`。
形式化陈述：coe_monoidHom_mk (s : G ->* E) (hs : Function.RightInverse s S.rightHom) :
 (mk s hs : G ->* E) = s
参数：s : G ->* E；hs : Function.RightInverse s S.rightHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.Splitting.instMonoidHomClass`：∀ {N : Type u_1} {E : Type 
u_2} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (S 
: GroupExtension N E G), MonoidHo…
-/
theorem coe_monoidHom_mk (s : G →* E) (hs : Function.RightInverse s S.rightHom) :
    (mk s hs : G →* E) = s := rfl

variable (s : S.Splitting)

@[to_additive (attr := simp)]
/-
**GroupExtension.Splitting.rightHom_splitting** 是 Mathlib 中的一个定理，位于命名空间 `GroupEx
tension.Splitting`。
形式化陈述：rightHom_splitting (g : G) : S.rightHom (s g) = g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupExtension.Splitting.rightInverse_rightHom`：∀ {N : Type u_1} {E : Ty
pe u_2} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   
{S : GroupExtension N E G} (self : S…
-/
theorem rightHom_splitting (g : G) : S.rightHom (s g) = g := s.rightInverse_rightHom g

@[to_additive (attr := simp)]
/-
**GroupExtension.Splitting.rightHom_comp_splitting** 是 Mathlib 中的一个定理，位于命名空间 `Gr
oupExtension.Splitting`。
形式化陈述：rightHom_comp_splitting : S.rightHom.comp s = MonoidHom.id G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `GroupExtension.Splitting.instMonoidHomClass`：∀ {N : Type u_1} {E : Type 
u_2} {G : Type u_3} [inst : Group N] [inst_1 : Group E] [inst_2 : Group G]   (S 
: GroupExtension N E G), MonoidHo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupExtension.Splitting.rightHom_splitting`：rightHom_splitting (g : G) 
: S.rightHom (s g) = g
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightHom_comp_splitting : S.rightHom.comp s = MonoidHom.id G := by
  ext g
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MonoidHom.coe_coe, rightHom_splitting]

end Splitting

/-- A splitting of an extension `S` is `N`-conjugate to another iff there exists `n : N` such that
the section homomorphism is a conjugate of the other section homomorphism by `S.inl n`. -/
@[to_additive
/-- A splitting of an extension `S` is `N`-conjugate to another iff there exists `n : N` such
that the section homomorphism is a conjugate of the other section homomorphism by `S.inl n`. -/]
/-
**GroupExtension.IsConj** 是 Mathlib 中的一个定义，位于命名空间 `GroupExtension`。
形式化陈述：IsConj (s s' : S.Splitting) : Prop
参数：s s' : S.Splitting。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsConj (s s' : S.Splitting) : Prop := ∃ n : N, s = fun g ↦ S.inl n * s' g * (S.inl n)⁻¹

end GroupExtension

namespace SemidirectProduct

variable [Group G] [Group N] (φ : G →* MulAut N)

/-- The group extension associated to the semidirect product -/
/-
**SemidirectProduct.toGroupExtension** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduc
t`。
形式化陈述：toGroupExtension : GroupExtension N (N ⋊[φ] G) G where inl
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SemidirectProduct.inl_injective`：inl_injective : Function.Injective (inl
 : N -> N ⋊[φ] G)
· 使用定理 `SemidirectProduct.range_inl_eq_ker_rightHom`：range_inl_eq_ker_rightHom :
 (inl : N ->* N ⋊[φ] G).range = rightHom.ker
· 使用定理 `SemidirectProduct.rightHom_surjective`：rightHom_surjective : Function.Su
rjective (rightHom : N ⋊[φ] G -> G)

--- 原说明 ---
The group extension associated to the semidirect product
-/
def toGroupExtension : GroupExtension N (N ⋊[φ] G) G where
  inl := inl
  inl_injective := inl_injective
  range_inl_eq_ker_rightHom := range_inl_eq_ker_rightHom
  rightHom := rightHom
  rightHom_surjective := rightHom_surjective
/-
**SemidirectProduct.toGroupExtension_inl** 是 Mathlib 中的一个定理，位于命名空间 `SemidirectPr
oduct`。
形式化陈述：toGroupExtension_inl : (toGroupExtension φ).inl = SemidirectProduct.inl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toGroupExtension_inl : (toGroupExtension φ).inl = SemidirectProduct.inl := rfl
/-
**SemidirectProduct.toGroupExtension_rightHom** 是 Mathlib 中的一个定理，位于命名空间 `Semidir
ectProduct`。
形式化陈述：toGroupExtension_rightHom : (toGroupExtension φ).rightHom = SemidirectProd
uct.rightHom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toGroupExtension_rightHom : (toGroupExtension φ).rightHom = SemidirectProduct.rightHom :=
  rfl

/-- A canonical splitting of the group extension associated to the semidirect product -/
/-
**SemidirectProduct.inr_splitting** 是 Mathlib 中的一个定义，位于命名空间 `SemidirectProduct`。
形式化陈述：inr_splitting : (toGroupExtension φ).Splitting where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SemidirectProduct.rightHom_inr`：rightHom_inr (g : G) : rightHom (inr g :
 N ⋊[φ] G) = g

--- 原说明 ---
A canonical splitting of the group extension associated to the semidirect produc
t
-/
def inr_splitting : (toGroupExtension φ).Splitting where
  __ := inr
  rightInverse_rightHom := rightHom_inr

end SemidirectProduct

