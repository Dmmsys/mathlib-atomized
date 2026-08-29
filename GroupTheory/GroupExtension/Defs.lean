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
      ↗ E ↘
1 → N ↓ G → 1
      ↘ E' ↗

For additive groups:
      ↗ E ↘
0 → N ↓ G → 0
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

/--
Definition of `AddGroupExtension` / `AddGroupExtension` 的定义

English:
structure AddGroupExtension
  parameters: [AddGroup N] [AddGroup E] [AddGroup G]
  axioms and operations (5):
    - inl : N ->+ E
    - rightHom : E ->+ G
    - inl_injective : Function.Injective inl
    - range_inl_eq_ker_rightHom : inl.range = rightHom.ker
    - rightHom_surjective : Function.Surjective rightHom

中文:
结构 AddGroupExtension
  参数: [AddGroup N] [AddGroup E] [AddGroup G]
  公理与运算 (5 个):
    - inl : N ->+ E
    - rightHom : E ->+ G
    - inl_injective : Function.Injective inl
    - range_inl_eq_ker_rightHom : inl.range = rightHom.ker
    - rightHom_surjective : Function.Surjective rightHom
-/
structure AddGroupExtension [AddGroup N] [AddGroup E] [AddGroup G] where
  /-- The inclusion homomorphism `N →+ E` -/
  inl : N ->+ E
  /-- The projection homomorphism `E →+ G` -/
  rightHom : E ->+ G
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom

/-- `GroupExtension N E G` is a short exact sequence of groups `1 → N → E → G → 1`. -/
@[to_additive]
/--
Definition of `GroupExtension` / `GroupExtension` 的定义

English:
structure GroupExtension
  parameters: [Group N] [Group E] [Group G]
  axioms and operations (5):
    - inl : N ->* E
    - rightHom : E ->* G
    - inl_injective : Function.Injective inl
    - range_inl_eq_ker_rightHom : inl.range = rightHom.ker
    - rightHom_surjective : Function.Surjective rightHom

中文:
结构 GroupExtension
  参数: [Group N] [Group E] [Group G]
  公理与运算 (5 个):
    - inl : N ->* E
    - rightHom : E ->* G
    - inl_injective : Function.Injective inl
    - range_inl_eq_ker_rightHom : inl.range = rightHom.ker
    - rightHom_surjective : Function.Surjective rightHom
-/
structure GroupExtension [Group N] [Group E] [Group G] where
  /-- The inclusion homomorphism `N →* E` -/
  inl : N ->* E
  /-- The projection homomorphism `E →* G` -/
  rightHom : E ->* G
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  range_inl_eq_ker_rightHom : inl.range = rightHom.ker
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom

variable {N E G}

namespace AddGroupExtension

variable [AddGroup N] [AddGroup E] [AddGroup G] (S : AddGroupExtension N E G)

/--
Definition of `Equiv` / `Equiv` 的定义

English:
structure Equiv
  parameters: {E' : Type*} [AddGroup E'] (S' : AddGroupExtension N E' G)
  extends: E ≃+ E'
  axioms and operations (2):
    - inl_comm : toAddEquiv ∘ S.inl = S'.inl
    - rightHom_comm : S'.rightHom ∘ toAddEquiv = S.rightHom

中文:
结构 Equiv
  参数: {E' : 类型} [AddGroup E'] (S' : AddGroupExtension N E' G)
  继承: E ≃+ E'
  公理与运算 (2 个):
    - inl_comm : toAddEquiv ∘ S.inl = S'.inl
    - rightHom_comm : S'.rightHom ∘ toAddEquiv = S.rightHom
-/
structure Equiv {E' : Type*} [AddGroup E'] (S' : AddGroupExtension N E' G) extends E ≃+ E' where
  /-- The left-hand side of the diagram commutes. -/
  inl_comm : toAddEquiv ∘ S.inl = S'.inl
  /-- The right-hand side of the diagram commutes. -/
  rightHom_comm : S'.rightHom ∘ toAddEquiv = S.rightHom

/--
Definition of `Section` / `Section` 的定义

English:
structure Section
  parameters: where
  axioms and operations (2):
    - toFun : G -> E
    - rightInverse_rightHom : Function.RightInverse toFun S.rightHom

中文:
结构 Section
  参数: where
  公理与运算 (2 个):
    - toFun : G -> E
    - rightInverse_rightHom : Function.RightInverse toFun S.rightHom
-/
structure Section where
  /-- The underlying function -/
  toFun : G -> E
  /-- `Section` is a right inverse to `S.rightHom` -/
  rightInverse_rightHom : Function.RightInverse toFun S.rightHom

/--
Definition of `Splitting` / `Splitting` 的定义

English:
structure Splitting
  parameters: extends G ->+ E, S.Section
  extends: G ->+ E, S.Section
  (no additional axioms)

中文:
结构 Splitting
  参数: extends G ->+ E, S.Section
  继承: G ->+ E, S.Section
  (无附加公理)
-/
structure Splitting extends G ->+ E, S.Section

/-- A splitting of an additive group extension as a (set-theoretic) section. -/
add_decl_doc Splitting.toSection

end AddGroupExtension

namespace GroupExtension

variable [Group N] [Group E] [Group G] (S : GroupExtension N E G)

/-- The range of the inclusion map is a normal subgroup. -/
@[to_additive /-- The range of the inclusion map is a normal additive subgroup. -/]
/--
Instance `normal_inl_range` / 实例 `normal_inl_range`

English:
instance normal_inl_range
  signature: : S.inl.range.Normal
  body: S.range_inl_eq_ker_rightHom ▸ S.rightHom.normal_ker

@[to_additive (attr := simp)]

中文:
实例 normal_inl_range
  签名: : S.inl.range.Normal
  定义体: S.range_inl_eq_ker_rightHom ▸ S.rightHom.normal_ker

@[to_additive (attr := simp)]

Depends on / 依赖: S.range_inl_eq_ker_rightHom, S.rightHom.normal_ker, normal_ker, range_inl_eq_ker_rightHom, rightHom
-/
instance normal_inl_range : S.inl.range.Normal :=
  S.range_inl_eq_ker_rightHom ▸ S.rightHom.normal_ker

@[to_additive (attr := simp)]
/--
theorem `rightHom_inl` / 定理 `rightHom_inl`

English:
theorem rightHom_inl
  given: (n : N)
  statement: S.rightHom (S.inl n) = 1
  proof: by
  rw [← MonoidHom.mem_ker]; rw [← S.range_inl_eq_ker_rightHom]; rw [MonoidHom.mem_range]
  exact exists_apply_eq_apply S.inl n

@[to_additive (attr := simp)]

中文:
定理 rightHom_inl
  条件: (n : N)
  结论: S.rightHom (S.inl n) = 1
  证明: by
  rw [← MonoidHom.mem_ker]; rw [← S.range_inl_eq_ker_rightHom]; rw [MonoidHom.mem_range]
  exact exists_apply_eq_apply S.inl n

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, MonoidHom.mem_range, S.inl, S.range_inl_eq_ker_rightHom, exists_apply_eq_apply, mem_ker, mem_range, range_inl_eq_ker_rightHom
-/
theorem rightHom_inl (n : N) : S.rightHom (S.inl n) = 1 := by
  rw [← MonoidHom.mem_ker]; rw [← S.range_inl_eq_ker_rightHom]; rw [MonoidHom.mem_range]
  exact exists_apply_eq_apply S.inl n

@[to_additive (attr := simp)]
/--
theorem `rightHom_comp_inl` / 定理 `rightHom_comp_inl`

English:
theorem rightHom_comp_inl
  statement: S.rightHom.comp S.inl = 1
  proof: by
  ext n
  rw [MonoidHom.one_apply]; rw [MonoidHom.comp_apply]
  exact S.rightHom_inl n

中文:
定理 rightHom_comp_inl
  结论: S.rightHom.comp S.inl = 1
  证明: by
  ext n
  rw [MonoidHom.one_apply]; rw [MonoidHom.comp_apply]
  exact S.rightHom_inl n

Depends on / 依赖: MonoidHom, MonoidHom.comp_apply, MonoidHom.one_apply, S.rightHom_inl, comp_apply, one_apply, rightHom_inl
-/
theorem rightHom_comp_inl : S.rightHom.comp S.inl = 1 := by
  ext n
  rw [MonoidHom.one_apply]; rw [MonoidHom.comp_apply]
  exact S.rightHom_inl n

/--
Definition of `conjAct` / `conjAct` 的定义

English:
definition conjAct
  signature: : E ->* MulAut N where
  body: (MonoidHom.ofInjective S.inl_injective).trans
    (MulAut.conjNormal e).trans (MonoidHom.ofInjective S.inl_injective).symm
  map_one' := by
    ext _
    simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' _ _ := by
    ext _
    simp only [map_mul, MulE

中文:
定义 conjAct
  签名: : E ->* MulAut N where
  定义体: (MonoidHom.ofInjective S.inl_injective).trans
    (MulAut.conjNormal e).trans (MonoidHom.ofInjective S.inl_injective).symm
  map_one' := by
    ext _
    simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' _ _ := by
    ext _
    simp only [map_mul, MulE

Depends on / 依赖: MonoidHom, MonoidHom.ofInjective, S.inl_injective, inl_injective, ofInjective
-/
noncomputable def conjAct : E ->* MulAut N where
toFun e := (MonoidHom.ofInjective S.inl_injective).trans
    (MulAut.conjNormal e).trans (MonoidHom.ofInjective S.inl_injective).symm
  map_one' := by
    ext _
    simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' _ _ := by
    ext _
    simp only [map_mul, MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.apply_symm_apply]

/--
theorem `inl_conjAct_comm` / 定理 `inl_conjAct_comm`

English:
theorem inl_conjAct_comm
  given: {e : E} {n : N}
  statement: S.inl (S.conjAct e n) = e * S.inl n * e⁻¹
  proof: by
  simp only [conjAct, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

中文:
定理 inl_conjAct_comm
  条件: {e : E} {n : N}
  结论: S.inl (S.conjAct e n) = e * S.inl n * e⁻¹
  证明: by
  simp only [conjAct, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

Depends on / 依赖: MonoidHom, MonoidHom.apply_ofInjective_symm, MonoidHom.coe_mk, MonoidHom.ofInjective_apply, MulAut, MulAut.conjNormal_apply, MulEquiv, MulEquiv.trans_apply, OneHom, OneHom.coe_mk, apply_ofInjective_symm, coe_mk, conjAct, conjNormal_apply, ofInjective_apply, trans_apply
-/
theorem inl_conjAct_comm {e : E} {n : N} : S.inl (S.conjAct e n) = e * S.inl n * e⁻¹ := by
  simp only [conjAct, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]

/-- `GroupExtension`s are equivalent iff there is an isomorphism making a commuting diagram.
  Use `GroupExtension.Equiv.ofMonoidHom` in `Mathlib/GroupTheory/GroupExtension/Basic.lean` to
  construct an equivalence without providing the inverse map. -/
@[to_additive]
/--
Definition of `Equiv` / `Equiv` 的定义

English:
structure Equiv
  parameters: {E' : Type*} [Group E'] (S' : GroupExtension N E' G)
  extends: E ≃* E'
  axioms and operations (2):
    - inl_comm : toMulEquiv ∘ S.inl = S'.inl
    - rightHom_comm : S'.rightHom ∘ toMulEquiv = S.rightHom

中文:
结构 Equiv
  参数: {E' : 类型} [Group E'] (S' : GroupExtension N E' G)
  继承: E ≃* E'
  公理与运算 (2 个):
    - inl_comm : toMulEquiv ∘ S.inl = S'.inl
    - rightHom_comm : S'.rightHom ∘ toMulEquiv = S.rightHom
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (S.Equiv S') E E'
  body: equiv.toMulEquiv
  inv equiv := equiv.toMulEquiv.symm
  left_inv equiv := equiv.left_inv
  right_inv equiv := equiv.right_inv
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ h _ => by
    congr
    rw [MulEquiv.ext_iff]
    exact congrFun h

@[to_additive]

中文:
实例 :
  签名: EquivLike (S.Equiv S') E E'
  定义体: equiv.toMulEquiv
  inv equiv := equiv.toMulEquiv.symm
  left_inv equiv := equiv.left_inv
  right_inv equiv := equiv.right_inv
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ h _ => by
    congr
    rw [MulEquiv.ext_iff]
    exact congrFun h

@[to_additive]

Depends on / 依赖: equiv.toMulEquiv, toMulEquiv
-/
instance : EquivLike (S.Equiv S') E E' where
  coe equiv := equiv.toMulEquiv
  inv equiv := equiv.toMulEquiv.symm
  left_inv equiv := equiv.left_inv
  right_inv equiv := equiv.right_inv
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ h _ => by
    congr
    rw [MulEquiv.ext_iff]
    exact congrFun h

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulEquivClass (S.Equiv S') E E'
  body: equiv.map_mul'

中文:
实例 :
  签名: MulEquivClass (S.Equiv S') E E'
  定义体: equiv.map_mul'

Depends on / 依赖: equiv.map_mul, map_mul
-/
instance : MulEquivClass (S.Equiv S') E E' where
  map_mul equiv := equiv.map_mul'

variable (equiv : S.Equiv S')

@[to_additive (attr := simp)]
/--
theorem `toMulEquiv_eq_coe` / 定理 `toMulEquiv_eq_coe`

English:
theorem toMulEquiv_eq_coe
  statement: equiv.toMulEquiv = equiv
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toMulEquiv_eq_coe
  结论: equiv.toMulEquiv = equiv
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toMulEquiv_eq_coe : equiv.toMulEquiv = equiv := rfl

@[to_additive (attr := simp)]
/--
theorem `coe_toMulEquiv` / 定理 `coe_toMulEquiv`

English:
theorem coe_toMulEquiv
  statement: ⇑(equiv : E ≃* E') = equiv
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_toMulEquiv
  结论: ⇑(equiv : E ≃* E') = equiv
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_toMulEquiv : ⇑(equiv : E ≃* E') = equiv := rfl

@[to_additive (attr := simp)]
/--
theorem `map_inl` / 定理 `map_inl`

English:
theorem map_inl
  given: (n : N)
  statement: equiv (S.inl n) = S'.inl n
  proof: congrFun equiv.inl_comm n

@[to_additive (attr := simp)]

中文:
定理 map_inl
  条件: (n : N)
  结论: equiv (S.inl n) = S'.inl n
  证明: congrFun equiv.inl_comm n

@[to_additive (attr := simp)]

Depends on / 依赖: equiv.inl_comm, inl_comm
-/
theorem map_inl (n : N) : equiv (S.inl n) = S'.inl n := congrFun equiv.inl_comm n

@[to_additive (attr := simp)]
/--
theorem `rightHom_map` / 定理 `rightHom_map`

English:
theorem rightHom_map
  given: (e : E)
  statement: S'.rightHom (equiv e) = S.rightHom e
  proof: congrFun equiv.rightHom_comm e

中文:
定理 rightHom_map
  条件: (e : E)
  结论: S'.rightHom (equiv e) = S.rightHom e
  证明: congrFun equiv.rightHom_comm e

Depends on / 依赖: equiv.rightHom_comm, rightHom_comm
-/
theorem rightHom_map (e : E) : S'.rightHom (equiv e) = S.rightHom e :=
  congrFun equiv.rightHom_comm e

/-- The inverse of an equivalence of group extensions is an equivalence. -/
@[to_additive /-- The inverse of an equivalence of additive group extensions is an equivalence. -/]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : S'.Equiv S where
  body: equiv.toMulEquiv.symm
  inl_comm := by rw [MulEquiv.symm_comp_eq, ← equiv.inl_comm]
  rightHom_comm := by rw [MulEquiv.comp_symm_eq, ← equiv.rightHom_comm]

中文:
定义 symm
  签名: : S'.Equiv S where
  定义体: equiv.toMulEquiv.symm
  inl_comm := by rw [MulEquiv.symm_comp_eq, ← equiv.inl_comm]
  rightHom_comm := by rw [MulEquiv.comp_symm_eq, ← equiv.rightHom_comm]

Depends on / 依赖: equiv.toMulEquiv.symm, toMulEquiv
-/
def symm : S'.Equiv S where
  __ := equiv.toMulEquiv.symm
  inl_comm := by rw [MulEquiv.symm_comp_eq, ← equiv.inl_comm]
  rightHom_comm := by rw [MulEquiv.comp_symm_eq, ← equiv.rightHom_comm]

/-- See Note [custom simps projection]. -/
@[to_additive /-- See Note [custom simps projection]. -/]
/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: : E' -> E
  body: equiv.symm

@[to_additive (attr := simp)]

中文:
定义 Simps.symm_apply
  签名: : E' -> E
  定义体: equiv.symm

@[to_additive (attr := simp)]
-/
def Simps.symm_apply : E' -> E := equiv.symm

@[to_additive (attr := simp)]
/--
theorem `coe_symm` / 定理 `coe_symm`

English:
theorem coe_symm
  statement: (equiv : E ≃* E').symm = equiv.symm
  proof: rfl

initialize_simps_projections AddGroupExtension.Equiv (toFun -> apply, invFun -> symm_apply)
initialize_simps_projections Equiv (toFun -> apply, invFun -> symm_apply)

中文:
定理 coe_symm
  结论: (equiv : E ≃* E').symm = equiv.symm
  证明: rfl

initialize_simps_projections AddGroupExtension.Equiv (toFun -> apply, invFun -> symm_apply)
initialize_simps_projections Equiv (toFun -> apply, invFun -> symm_apply)
-/
theorem coe_symm : (equiv : E ≃* E').symm = equiv.symm := rfl

initialize_simps_projections AddGroupExtension.Equiv (toFun -> apply, invFun -> symm_apply)
initialize_simps_projections Equiv (toFun -> apply, invFun -> symm_apply)

attribute [simps! symm_apply] AddGroupExtension.Equiv.symm
attribute [simps! symm_apply] symm

/-- The composition of monoid isomorphisms associated to equivalences of group extensions gives
another equivalence. -/
@[to_additive (attr := simps!)
/-- The composition of monoid isomorphisms associated to equivalences of additive group
extensions gives another equivalence. -/]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {E'' : Type*} [Group E''] {S'' : GroupExtension N E'' G} (equiv' : S'.Equiv S'')
  body: equiv.toMulEquiv.trans equiv'.toMulEquiv
  inl_comm := by rw [MulEquiv.coe_trans, Function.comp_assoc, equiv.inl_comm, equiv'.inl_comm]
  rightHom_comm := by
    rw [MulEquiv.coe_trans]; rw [← Function.comp_assoc]; rw [equiv'.rightHom_comm]; rw [equiv.rightHom_comm]

中文:
定义 trans
  签名: {E'' : 类型} [Group E''] {S'' : GroupExtension N E'' G} (equiv' : S'.Equiv S'')
  定义体: equiv.toMulEquiv.trans equiv'.toMulEquiv
  inl_comm := by rw [MulEquiv.coe_trans, Function.comp_assoc, equiv.inl_comm, equiv'.inl_comm]
  rightHom_comm := by
    rw [MulEquiv.coe_trans]; rw [← Function.comp_assoc]; rw [equiv'.rightHom_comm]; rw [equiv.rightHom_comm]

Depends on / 依赖: equiv.toMulEquiv.trans, toMulEquiv
-/
def trans {E'' : Type*} [Group E''] {S'' : GroupExtension N E'' G} (equiv' : S'.Equiv S'') :
    S.Equiv S'' where
  __ := equiv.toMulEquiv.trans equiv'.toMulEquiv
  inl_comm := by rw [MulEquiv.coe_trans, Function.comp_assoc, equiv.inl_comm, equiv'.inl_comm]
  rightHom_comm := by
    rw [MulEquiv.coe_trans]; rw [← Function.comp_assoc]; rw [equiv'.rightHom_comm]; rw [equiv.rightHom_comm]

variable (S)
/-- A group extension is equivalent to itself. -/
@[to_additive (attr := simps!) /-- An additive group extension is equivalent to itself. -/]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : S.Equiv S where
  body: MulEquiv.refl E
  inl_comm := rfl
  rightHom_comm := rfl

中文:
定义 refl
  签名: : S.Equiv S where
  定义体: MulEquiv.refl E
  inl_comm := rfl
  rightHom_comm := rfl

Depends on / 依赖: MulEquiv, MulEquiv.refl
-/
def refl : S.Equiv S where
  __ := MulEquiv.refl E
  inl_comm := rfl
  rightHom_comm := rfl

end Equiv

/-- `Section` of a group extension is a right inverse to `S.rightHom`. -/
@[to_additive]
/--
Definition of `Section` / `Section` 的定义

English:
structure Section
  parameters: where
  axioms and operations (2):
    - toFun : G -> E
    - rightInverse_rightHom : Function.RightInverse toFun S.rightHom

中文:
结构 Section
  参数: where
  公理与运算 (2 个):
    - toFun : G -> E
    - rightInverse_rightHom : Function.RightInverse toFun S.rightHom
-/
structure Section where
  /-- The underlying function -/
  toFun : G -> E
  /-- `Section` is a right inverse to `S.rightHom` -/
  rightInverse_rightHom : Function.RightInverse toFun S.rightHom

namespace Section

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike S.Section G E
  body: toFun
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr

中文:
实例 :
  签名: FunLike S.Section G E
  定义体: toFun
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr
-/
instance : FunLike S.Section G E where
  coe := toFun
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr

variable {S}

@[to_additive (attr := simp)]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (σ : G -> E) (hσ : Function.RightInverse σ S.rightHom)
  statement: (mk σ hσ : G -> E) = σ
  proof: rfl

中文:
定理 coe_mk
  条件: (σ : G -> E) (hσ : Function.RightInverse σ S.rightHom)
  结论: (mk σ hσ : G -> E) = σ
  证明: rfl
-/
theorem coe_mk (σ : G -> E) (hσ : Function.RightInverse σ S.rightHom) : (mk σ hσ : G -> E) = σ := rfl

variable (σ : S.Section)

@[to_additive (attr := simp)]
/--
theorem `rightHom_section` / 定理 `rightHom_section`

English:
theorem rightHom_section
  given: (g : G)
  statement: S.rightHom (σ g) = g
  proof: σ.rightInverse_rightHom g

@[to_additive (attr := simp)]

中文:
定理 rightHom_section
  条件: (g : G)
  结论: S.rightHom (σ g) = g
  证明: σ.rightInverse_rightHom g

@[to_additive (attr := simp)]

Depends on / 依赖: rightInverse_rightHom
-/
theorem rightHom_section (g : G) : S.rightHom (σ g) = g := σ.rightInverse_rightHom g

@[to_additive (attr := simp)]
/--
theorem `rightHom_comp_section` / 定理 `rightHom_comp_section`

English:
theorem rightHom_comp_section
  statement: S.rightHom ∘ σ = id
  proof: σ.rightInverse_rightHom.comp_eq_id

中文:
定理 rightHom_comp_section
  结论: S.rightHom ∘ σ = id
  证明: σ.rightInverse_rightHom.comp_eq_id

Depends on / 依赖: comp_eq_id, rightInverse_rightHom, rightInverse_rightHom.comp_eq_id
-/
theorem rightHom_comp_section : S.rightHom ∘ σ = id := σ.rightInverse_rightHom.comp_eq_id

end Section

/-- `Splitting` of a group extension is a section homomorphism. -/
@[to_additive]
/--
Definition of `Splitting` / `Splitting` 的定义

English:
structure Splitting
  parameters: extends G ->* E, S.Section
  extends: G ->* E, S.Section
  (no additional axioms)

中文:
结构 Splitting
  参数: extends G ->* E, S.Section
  继承: G ->* E, S.Section
  (无附加公理)
-/
structure Splitting extends G ->* E, S.Section

/-- A splitting of a group extension as a (set-theoretic) section. -/
add_decl_doc Splitting.toSection

namespace Splitting

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike S.Splitting G E
  body: s.toFun
  coe_injective := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

@[to_additive]

中文:
实例 :
  签名: FunLike S.Splitting G E
  定义体: s.toFun
  coe_injective := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

@[to_additive]

Depends on / 依赖: s.toFun
-/
instance : FunLike S.Splitting G E where
  coe s := s.toFun
  coe_injective := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidHomClass S.Splitting G E
  body: s.map_mul'
  map_one s := s.map_one'

中文:
实例 :
  签名: MonoidHomClass S.Splitting G E
  定义体: s.map_mul'
  map_one s := s.map_one'

Depends on / 依赖: map_mul, s.map_mul
-/
instance : MonoidHomClass S.Splitting G E where
  map_mul s := s.map_mul'
  map_one s := s.map_one'

variable {S}

@[to_additive (attr := simp)]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : G ->* E) (hs : Function.RightInverse s S.rightHom)
  statement: (mk s hs : G -> E) = s
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mk
  条件: (s : G ->* E) (hs : Function.RightInverse s S.rightHom)
  结论: (mk s hs : G -> E) = s
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mk (s : G ->* E) (hs : Function.RightInverse s S.rightHom) : (mk s hs : G -> E) = s := rfl

@[to_additive (attr := simp)]
/--
theorem `coe_monoidHom_mk` / 定理 `coe_monoidHom_mk`

English:
theorem coe_monoidHom_mk
  given: (s : G ->* E) (hs : Function.RightInverse s S.rightHom)
  proof: rfl

中文:
定理 coe_monoidHom_mk
  条件: (s : G ->* E) (hs : Function.RightInverse s S.rightHom)
  证明: rfl
-/
theorem coe_monoidHom_mk (s : G ->* E) (hs : Function.RightInverse s S.rightHom) :
    (mk s hs : G ->* E) = s := rfl

variable (s : S.Splitting)

@[to_additive (attr := simp)]
/--
theorem `rightHom_splitting` / 定理 `rightHom_splitting`

English:
theorem rightHom_splitting
  given: (g : G)
  statement: S.rightHom (s g) = g
  proof: s.rightInverse_rightHom g

@[to_additive (attr := simp)]

中文:
定理 rightHom_splitting
  条件: (g : G)
  结论: S.rightHom (s g) = g
  证明: s.rightInverse_rightHom g

@[to_additive (attr := simp)]

Depends on / 依赖: rightInverse_rightHom, s.rightInverse_rightHom
-/
theorem rightHom_splitting (g : G) : S.rightHom (s g) = g := s.rightInverse_rightHom g

@[to_additive (attr := simp)]
/--
theorem `rightHom_comp_splitting` / 定理 `rightHom_comp_splitting`

English:
theorem rightHom_comp_splitting
  statement: S.rightHom.comp s = MonoidHom.id G
  proof: by
  ext g
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MonoidHom.coe_coe, rightHom_splitting]

中文:
定理 rightHom_comp_splitting
  结论: S.rightHom.comp s = MonoidHom.id G
  证明: by
  ext g
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MonoidHom.coe_coe, rightHom_splitting]

Depends on / 依赖: MonoidHom, MonoidHom.coe_coe, MonoidHom.comp_apply, MonoidHom.id_apply, coe_coe, comp_apply, id_apply, rightHom_splitting
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
/--
Definition of `IsConj` / `IsConj` 的定义

English:
definition IsConj
  signature: (s s' : S.Splitting)
  body: exists n : N, s = fun g => S.inl n * s' g * (S.inl n)⁻¹

中文:
定义 IsConj
  签名: (s s' : S.Splitting)
  定义体: exists n : N, s = fun g => S.inl n * s' g * (S.inl n)⁻¹

Depends on / 依赖: S.inl
-/
def IsConj (s s' : S.Splitting) : Prop := exists n : N, s = fun g => S.inl n * s' g * (S.inl n)⁻¹

end GroupExtension

namespace SemidirectProduct

variable [Group G] [Group N] (φ : G ->* MulAut N)

/--
Definition of `toGroupExtension` / `toGroupExtension` 的定义

English:
definition toGroupExtension
  signature: : GroupExtension N (N ⋊[φ] G) G where
  body: inl
  inl_injective := inl_injective
  range_inl_eq_ker_rightHom := range_inl_eq_ker_rightHom
  rightHom := rightHom
  rightHom_surjective := rightHom_surjective

中文:
定义 toGroupExtension
  签名: : GroupExtension N (N ⋊[φ] G) G where
  定义体: inl
  inl_injective := inl_injective
  range_inl_eq_ker_rightHom := range_inl_eq_ker_rightHom
  rightHom := rightHom
  rightHom_surjective := rightHom_surjective
-/
def toGroupExtension : GroupExtension N (N ⋊[φ] G) G where
  inl := inl
  inl_injective := inl_injective
  range_inl_eq_ker_rightHom := range_inl_eq_ker_rightHom
  rightHom := rightHom
  rightHom_surjective := rightHom_surjective

/--
theorem `toGroupExtension_inl` / 定理 `toGroupExtension_inl`

English:
theorem toGroupExtension_inl
  statement: (toGroupExtension φ).inl = SemidirectProduct.inl
  proof: rfl

中文:
定理 toGroupExtension_inl
  结论: (toGroupExtension φ).inl = SemidirectProduct.inl
  证明: rfl
-/
theorem toGroupExtension_inl : (toGroupExtension φ).inl = SemidirectProduct.inl := rfl

/--
theorem `toGroupExtension_rightHom` / 定理 `toGroupExtension_rightHom`

English:
theorem toGroupExtension_rightHom
  statement: (toGroupExtension φ).rightHom = SemidirectProduct.rightHom
  proof: rfl

中文:
定理 toGroupExtension_rightHom
  结论: (toGroupExtension φ).rightHom = SemidirectProduct.rightHom
  证明: rfl
-/
theorem toGroupExtension_rightHom : (toGroupExtension φ).rightHom = SemidirectProduct.rightHom :=
  rfl

/--
Definition of `inr_splitting` / `inr_splitting` 的定义

English:
definition inr_splitting
  signature: : (toGroupExtension φ).Splitting where
  body: inr
  rightInverse_rightHom := rightHom_inr

中文:
定义 inr_splitting
  签名: : (toGroupExtension φ).Splitting where
  定义体: inr
  rightInverse_rightHom := rightHom_inr
-/
def inr_splitting : (toGroupExtension φ).Splitting where
  __ := inr
  rightInverse_rightHom := rightHom_inr

end SemidirectProduct
