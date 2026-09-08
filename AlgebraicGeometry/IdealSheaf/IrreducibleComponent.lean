/-
Copyright (c) 2026 Thomas Browning, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Subscheme structure on an irreducible component

We define the subscheme structure on an irreducible component of a Noetherian scheme. Typically,
one takes the reduced induced subscheme structure, but this will throw away information if the
irreducible component is not already reduced. Instead, we take the closed subscheme defined by
the kernel of the restriction to the complement of the union of the other irreducible components.
For example, if `X` is irreducible then this will give back the original scheme `X`.

## Main definition
* `AlgebraicGeometry.Scheme.irreducibleComponentIdeal`: The ideal sheaf data associated to an
  irreducible component of a Noetherian scheme.
* `AlgebraicGeometry.Scheme.irreducibleComponent`: The subscheme structure on an irreducible
  component of a Noetherian scheme.

## TODO

Prove that for affine schemes this subscheme structure is defined by the kernel of the
localization away from the union of the other minimal prime ideals.

-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) [IsNoetherian X]

/-- The complement of the irreducible components unequal to `Z` of a Noetherian scheme. -/
/-
**AlgebraicGeometry.Scheme.irreducibleComponentOpen** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme`。
形式化陈述：irreducibleComponentOpen : Opens X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement of the irreducible components unequal to `Z` of a Noetherian sche
me.
-/
def irreducibleComponentOpen : Opens X :=
  ⟨(⋃₀ (irreducibleComponents X \ {Z}))ᶜ, by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1⟩

/-- The ideal sheaf data associated to an irreducible component of a Noetherian scheme. -/
/-
**AlgebraicGeometry.Scheme.irreducibleComponentIdeal** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme`。
形式化陈述：irreducibleComponentIdeal : X.IdealSheafData where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_basicOpen`：∀ {X : Alge
braicGeometry.Scheme} (self : X.IdealSheafData) (U : ↑X.affineOpens)   (f : ↑(X.
presheaf.obj (Opposite.op ↑U))),   Ideal.map (Com…

--- 原说明 ---
The ideal sheaf data associated to an irreducible component of a Noetherian sche
me.
-/
def irreducibleComponentIdeal : X.IdealSheafData where
  __ := (irreducibleComponentOpen X Z).ι.ker
  supportSet := Z
  supportSet_eq_iInter_zeroLocus := by
    rw [← IdealSheafData.coe_support_eq_eq_iInter_zeroLocus, Hom.support_ker, Opens.range_ι]
    exact (closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents Z hZ).symm
/-
**AlgebraicGeometry.Scheme.irreducibleComponentIdeal_def** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme`。
形式化陈述：irreducibleComponentIdeal_def : irreducibleComponentIdeal X Z hZ = (irredu
cibleComponentOpen X Z).ι.ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.ext`：∀ {X : AlgebraicGeometry.Sc
heme} {I J : X.IdealSheafData}, I.ideal = J.ideal → I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irreducibleComponentIdeal_def :
    irreducibleComponentIdeal X Z hZ = (irreducibleComponentOpen X Z).ι.ker := by
  ext
  rfl

/-- The subscheme structure on an irreducible component of a Noetherian scheme. -/
/-
**AlgebraicGeometry.Scheme.irreducibleComponent** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：irreducibleComponent : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subscheme structure on an irreducible component of a Noetherian scheme.
-/
noncomputable def irreducibleComponent : Scheme :=
  (X.irreducibleComponentIdeal Z hZ).subscheme

/-- The inclusion from an irreducible component of a Noetherian scheme. -/
/-
**AlgebraicGeometry.Scheme.irreducibleComponent** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：irreducibleComponent : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion from an irreducible component of a Noetherian scheme.
-/
noncomputable def irreducibleComponentι : X.irreducibleComponent Z hZ ⟶ X :=
  (X.irreducibleComponentIdeal Z hZ).subschemeι
/-
**AlgebraicGeometry.Scheme.irreducibleComponent** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：irreducibleComponent : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma irreducibleComponentι_apply (x : X.irreducibleComponent Z hZ) :
    X.irreducibleComponentι Z hZ x = x.1 :=
  rfl
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsClosedImmersion (X.irreducibleComponentι Z hZ) :=
  inferInstanceAs (IsClosedImmersion (X.irreducibleComponentIdeal Z hZ).subschemeι)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IrreducibleSpace (X.irreducibleComponent Z hZ) :=
  Subtype.irreducibleSpace hZ.1

include hZ in
/-
**AlgebraicGeometry.Scheme.irreducibleComponentOpen_eq_top** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：irreducibleComponentOpen_eq_top [IrreducibleSpace X] : irreducibleComponen
tOpen X Z = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `irreducibleComponents_eq_singleton`：irreducibleComponents_eq_singleton [
IrreducibleSpace X] : irreducibleComponents X = {univ}
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem irreducibleComponentOpen_eq_top [IrreducibleSpace X] :
    irreducibleComponentOpen X Z = ⊤ := by
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
  simp [irreducibleComponentOpen, irreducibleComponents_eq_singleton, hZ]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IrreducibleSpace X] : CategoryTheory.IsIso (X.irreducibleComponentι Z hZ) := by
  have : CategoryTheory.IsIso (irreducibleComponentOpen X Z).ι := by
    rw [irreducibleComponentOpen_eq_top X Z hZ]
    exact X.topIso.isIso_hom
  rw [irreducibleComponentι, isIso_subschemeι_iff_eq_bot, irreducibleComponentIdeal_def,
    irreducibleComponentOpen_eq_top X Z hZ]
  exact X.topIso.hom.ker_eq_bot_of_isIso

end AlgebraicGeometry.Scheme

