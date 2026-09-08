/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Kernels
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Homology and exactness of short complexes of abelian groups

In this file, the homology of a short complex `S` of abelian groups is identified
with the quotient of `AddMonoidHom.ker S.g` by the image of the morphism
`S.abToCycles : S.X₁ →+ AddMonoidHom.ker S.g` induced by `S.f`.

The definitions are made in the `ShortComplex` namespace so as to enable dot notation.
The names contain the prefix `ab` in order to allow similar constructions for
other categories like `ModuleCat`.

## Main definitions
- `ShortComplex.abHomologyIso` identifies the homology of a short complex of abelian
  groups to an explicit quotient.
- `ShortComplex.ab_exact_iff` expresses that a short complex of abelian groups `S`
  is exact iff any element in the kernel of `S.g` belongs to the image of `S.f`.

-/

@[expose] public section

universe u

namespace CategoryTheory

namespace ShortComplex

variable (S : ShortComplex Ab.{u})

@[simp]
/-
**CategoryTheory.ShortComplex.ab_zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：ab_zero_apply (x : S.X₁) : S.g (S.f x) = 0
参数：x : S.X₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
-/
lemma ab_zero_apply (x : S.X₁) : S.g (S.f x) = 0 := by
  rw [← ConcreteCategory.comp_apply, S.zero]
  rfl

/-- The canonical additive morphism `S.X₁ →+ AddMonoidHom.ker S.g` induced by `S.f`. -/
@[simps!]
/-
**CategoryTheory.ShortComplex.abToCycles** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ShortComplex`。
形式化陈述：abToCycles : S.X₁ ->+ AddMonoidHom.ker S.g.hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.ab_zero_apply`：ab_zero_apply (x : S.X₁) : S.
g (S.f x) = 0

--- 原说明 ---
The canonical additive morphism `S.X₁ →+ AddMonoidHom.ker S.g` induced by `S.f`.
-/
def abToCycles : S.X₁ →+ AddMonoidHom.ker S.g.hom :=
    AddMonoidHom.mk' (fun x => ⟨S.f x, S.ab_zero_apply x⟩) (by aesop)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit left homology data of a short complex of abelian group that is
given by a kernel and a quotient given by the `AddMonoidHom` API. -/
@[simps]
/-
**CategoryTheory.ShortComplex.abLeftHomologyData** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：abLeftHomologyData : S.LeftHomologyData where K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit left homology data of a short complex of abelian group that is
given by a kernel and a quotient given by the `AddMonoidHom` API.
-/
def abLeftHomologyData : S.LeftHomologyData where
  K := AddCommGrpCat.of (AddMonoidHom.ker S.g.hom)
  H := AddCommGrpCat.of ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles)
  i := AddCommGrpCat.ofHom <| (AddMonoidHom.ker S.g.hom).subtype
  π := AddCommGrpCat.ofHom <| QuotientAddGroup.mk' _
  wi := by
    ext ⟨_, hx⟩
    exact hx
  hi := AddCommGrpCat.kernelIsLimit _
  wπ := by
    ext (x : S.X₁)
    dsimp
    rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
    apply exists_apply_eq_apply
  hπ := AddCommGrpCat.cokernelIsColimit (AddCommGrpCat.ofHom S.abToCycles)

@[simp]
/-
**CategoryTheory.ShortComplex.abLeftHomologyData_f'** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：abLeftHomologyData_f' : S.abLeftHomologyData.f' = AddCommGrpCat.ofHom S.ab
ToCycles
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma abLeftHomologyData_f' : S.abLeftHomologyData.f' = AddCommGrpCat.ofHom S.abToCycles := rfl

/-- Given a short complex `S` of abelian groups, this is the isomorphism between
the abstract `S.cycles` of the homology API and the more concrete description as
`AddMonoidHom.ker S.g`. -/
/-
**CategoryTheory.ShortComplex.abCyclesIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ShortComplex`。
形式化陈述：abCyclesIso : S.cycles ≅ AddCommGrpCat.of (AddMonoidHom.ker S.g.hom)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a short complex `S` of abelian groups, this is the isomorphism between
the abstract `S.cycles` of the homology API and the more concrete description as
`AddMonoidHom.ker S.g`.
-/
noncomputable def abCyclesIso : S.cycles ≅ AddCommGrpCat.of (AddMonoidHom.ker S.g.hom) :=
  S.abLeftHomologyData.cyclesIso

set_option backward.isDefEq.respectTransparency false in
-- This was a simp lemma until we made `AddCommGrpCat.coe_of` a simp lemma,
-- after which the simp normal form linter complains.
-- It was not used a simp lemma in Mathlib.
-- Possible solution: higher priority function coercions that remove the `of`?
-- @[simp]
/-
**CategoryTheory.ShortComplex.abCyclesIso_inv_apply_iCycles** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：abCyclesIso_inv_apply_iCycles (x : AddMonoidHom.ker S.g.hom) : S.iCycles (
S.abCyclesIso.inv x) = x
参数：x : AddMonoidHom.ker S.g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用引理 `CategoryTheory.ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles`
：cyclesIso_inv_comp_iCycles : h.cyclesIso.inv ≫ S.iCycles = h.i
-/
lemma abCyclesIso_inv_apply_iCycles (x : AddMonoidHom.ker S.g.hom) :
    S.iCycles (S.abCyclesIso.inv x) = x := by
  dsimp only [abCyclesIso]
  rw [← ConcreteCategory.comp_apply, S.abLeftHomologyData.cyclesIso_inv_comp_iCycles]
  rfl

/-- Given a short complex `S` of abelian groups, this is the isomorphism between
the abstract `S.homology` of the homology API and the more explicit
quotient of `AddMonoidHom.ker S.g` by the image of
`S.abToCycles : S.X₁ →+ AddMonoidHom.ker S.g`. -/
/-
**CategoryTheory.ShortComplex.abHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：abHomologyIso : S.homology ≅ AddCommGrpCat.of ((AddMonoidHom.ker S.g.hom) 
⧸ AddMonoidHom.range S.abToCycles)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a short complex `S` of abelian groups, this is the isomorphism between
the abstract `S.homology` of the homology API and the more explicit
quotient of `AddMonoidHom.ker S.g` by the image of
`S.abToCycles : S.X₁ →+ AddMonoidHom.ker S.g`.
-/
noncomputable def abHomologyIso : S.homology ≅
    AddCommGrpCat.of ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles) :=
  S.abLeftHomologyData.homologyIso

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ShortComplex.exact_iff_surjective_abToCycles** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：exact_iff_surjective_abToCycles : S.Exact ↔ Function.Surjective S.abToCycl
es
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyData.exact_iff_epi_f'`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.P
readditive C]   {S : CategoryTheory.ShortComplex C}…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用引理 `CategoryTheory.ShortComplex.abLeftHomologyData_f'`：abLeftHomologyData_f'
 : S.abLeftHomologyData.f' = AddCommGrpCat.ofHom S.abToCycles
· 使用定理 `AddCommGrpCat.epi_iff_surjective`：∀ {A B : AddCommGrpCat} (f : A ⟶ B), C
ategoryTheory.Epi f ↔ Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom 
f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma exact_iff_surjective_abToCycles :
    S.Exact ↔ Function.Surjective S.abToCycles := by
  rw [S.abLeftHomologyData.exact_iff_epi_f', abLeftHomologyData_f',
    AddCommGrpCat.epi_iff_surjective]
  rfl
/-
**CategoryTheory.ShortComplex.ab_exact_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ShortComplex`。
形式化陈述：ab_exact_iff : S.Exact ↔ forall (x₂ : S.X₂) (_ : S.g x₂ = 0), exists (x₁ :
 S.X₁), S.f x₁ = x₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_surjective_abToCycles`：exact_iff_s
urjective_abToCycles : S.Exact ↔ Function.Surjective S.abToCycles
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ShortComplex.abToCycles_apply_coe`：∀ (S : CategoryTheory.
ShortComplex Ab) (x : ↑S.X₁), ↑(S.abToCycles x) = (CategoryTheory.ConcreteCatego
ry.hom S.f) x
-/
lemma ab_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ := by
  rw [exact_iff_surjective_abToCycles]
  constructor
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h ⟨x₂, hx₂⟩
    exact ⟨x₁, by simpa only [Subtype.ext_iff, abToCycles_apply_coe] using hx₁⟩
  · rintro h ⟨x₂, hx₂⟩
    obtain ⟨x₁, rfl⟩ := h x₂ hx₂
    exact ⟨x₁, rfl⟩
/-
**CategoryTheory.ShortComplex.ab_exact_iff_function_exact** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ShortComplex`。
形式化陈述：ab_exact_iff_function_exact : S.Exact ↔ Function.Exact S.f S.g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.ab_exact_iff`：ab_exact_iff : S.Exact ↔ foral
l (x₂ : S.X₂) (_ : S.g x₂ = 0), exists (x₁ : S.X₁), S.f x₁ = x₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ShortComplex.ab_zero_apply`：ab_zero_apply (x : S.X₁) : S.
g (S.f x) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
-/
lemma ab_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [S.ab_exact_iff]
  apply forall_congr'
  intro x₂
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨x₁, rfl⟩
    simp only [ab_zero_apply]
  · tauto

variable {S}
/-
**CategoryTheory.ShortComplex.ab_exact_iff_ker_le_range** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：ab_exact_iff_ker_le_range : S.Exact ↔ S.g.hom.ker <= S.f.hom.range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.ab_exact_iff`：ab_exact_iff : S.Exact ↔ foral
l (x₂ : S.X₂) (_ : S.g x₂ = 0), exists (x₁ : S.X₁), S.f x₁ = x₂
-/
lemma ab_exact_iff_ker_le_range : S.Exact ↔ S.g.hom.ker ≤ S.f.hom.range := S.ab_exact_iff
/-
**CategoryTheory.ShortComplex.ab_exact_iff_range_eq_ker** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：ab_exact_iff_range_eq_ker : S.Exact ↔ S.f.hom.range = S.g.hom.ker
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.ab_exact_iff_ker_le_range`：ab_exact_iff_ker_
le_range : S.Exact ↔ S.g.hom.ker <= S.f.hom.range
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AddMonoidHom.mem_ker`：∀ {G : Type u_1} [inst : AddGroup G] {M : Type u_7
} [inst_1 : AddZeroClass M] {f : G →+ M} {x : G}, x ∈ f.ker ↔ f x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma ab_exact_iff_range_eq_ker : S.Exact ↔ S.f.hom.range = S.g.hom.ker := by
  rw [ab_exact_iff_ker_le_range]
  constructor
  · intro h
    refine le_antisymm ?_ h
    rintro _ ⟨x₁, rfl⟩
    rw [AddMonoidHom.mem_ker, ← ConcreteCategory.comp_apply, S.zero]
    rfl
  · intro h
    rw [h]

alias ⟨Exact.ab_range_eq_ker, _⟩ := ab_exact_iff_range_eq_ker

/-- In an exact sequence of abelian groups, if the first and last groups are finite, then so is the
middle one. -/
/-
**CategoryTheory.ShortComplex.Exact.ab_finite** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.ShortComplex.Exact`。
形式化陈述：∀ {S : CategoryTheory.ShortComplex Ab}, S.Exact → ∀ [Finite ↑S.X₁] [Finite
 ↑S.X₃], Finite ↑S.X₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.Exact.ab_range_eq_ker`：∀ {S : CategoryTheory
.ShortComplex Ab}, S.Exact → (AddCommGrpCat.Hom.hom S.f).range = (AddCommGrpCat.
Hom.hom S.g).ker
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `AddSubgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : AddGroup G] (
K : AddSubgroup G) [Finite G], Finite ↥K
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AddMonoidHom.normal_ker`：∀ {G : Type u_1} [inst : AddGroup G] {M : Type 
u_7} [inst_1 : AddZeroClass M] (f : G →+ M), f.ker.Normal
· 使用定理 `Finite.of_addSubgroup_quotient`：∀ {G : Type u_2} [inst : AddGroup G] (H 
: AddSubgroup G) [Finite ↥H] [Finite (G ⧸ H)], Finite G

--- 原说明 ---
In an exact sequence of abelian groups, if the first and last groups are finite,
 then so is the
middle one.
-/
lemma Exact.ab_finite {S : ShortComplex Ab.{u}} (hS : S.Exact) [Finite S.X₁] [Finite S.X₃] :
    Finite S.X₂ := by
  have : Finite S.f.hom.range := Set.finite_range _
  have : Finite (S.X₂ ⧸ S.f.hom.range) := by
    rw [hS.ab_range_eq_ker]
    exact .of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).toEquiv.symm
  exact .of_addSubgroup_quotient (H := S.f.hom.range)
/-
**CategoryTheory.ShortComplex.ShortExact.ab_injective_f** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {S : CategoryTheory.ShortComplex Ab}, S.ShortExact → Function.Injective 
⇑(CategoryTheory.ConcreteCategory.hom S.f)
参数：CategoryTheory.ConcreteCategory.hom S.f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddCommGrpCat.mono_iff_injective`：∀ {A B : AddCommGrpCat} (f : A ⟶ B), C
ategoryTheory.Mono f ↔ Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom 
f)
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
-/
lemma ShortExact.ab_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  (AddCommGrpCat.mono_iff_injective _).1 hS.mono_f
/-
**CategoryTheory.ShortComplex.ShortExact.ab_surjective_g** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {S : CategoryTheory.ShortComplex Ab}, S.ShortExact → Function.Surjective
 ⇑(CategoryTheory.ConcreteCategory.hom S.g)
参数：CategoryTheory.ConcreteCategory.hom S.g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddCommGrpCat.epi_iff_surjective`：∀ {A B : AddCommGrpCat} (f : A ⟶ B), C
ategoryTheory.Epi f ↔ Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom 
f)
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
-/
lemma ShortExact.ab_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  (AddCommGrpCat.epi_iff_surjective _).1 hS.epi_g

/-- In a short exact sequence of abelian groups, the middle group is finite iff the first and last
are. -/
/-
**CategoryTheory.ShortComplex.ShortExact.ab_finite_iff** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：∀ {S : CategoryTheory.ShortComplex Ab}, S.ShortExact → (Finite ↑S.X₂ ↔ Fin
ite ↑S.X₁ ∧ Finite ↑S.X₃)
参数：Finite ↑S.X₂ ↔ Finite ↑S.X₁ ∧ Finite ↑S.X₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.ab_injective_f`：∀ {S : CategoryTh
eory.ShortComplex Ab}, S.ShortExact → Function.Injective ⇑(CategoryTheory.Concre
teCategory.hom S.f)
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.ab_surjective_g`：∀ {S : CategoryT
heory.ShortComplex Ab}, S.ShortExact → Function.Surjective ⇑(CategoryTheory.Conc
reteCategory.hom S.g)
· 使用定理 `CategoryTheory.ShortComplex.Exact.ab_finite`：∀ {S : CategoryTheory.Short
Complex Ab}, S.Exact → ∀ [Finite ↑S.X₁] [Finite ↑S.X₃], Finite ↑S.X₂
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…

--- 原说明 ---
In a short exact sequence of abelian groups, the middle group is finite iff the 
first and last
are.
-/
lemma ShortExact.ab_finite_iff {S : ShortComplex Ab.{u}} (hS : S.ShortExact) :
    Finite S.X₂ ↔ Finite S.X₁ ∧ Finite S.X₃ where
  mp _ := ⟨.of_injective _ hS.ab_injective_f, .of_surjective _ hS.ab_surjective_g⟩
  mpr | ⟨_, _⟩ => hS.exact.ab_finite

end ShortComplex

end CategoryTheory

