/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# The alternating constant complex

Given an object `X : C` and endomorphisms `φ, ψ : X ⟶ X` such that `φ ∘ ψ = ψ ∘ φ = 0`, this file
defines the periodic chain and cochain complexes
`... ⟶ X --φ--> X --ψ--> X --φ--> X --ψ--> 0` and `0 ⟶ X --ψ--> X --φ--> X --ψ--> X --φ--> ...`
(or more generally for any complex shape `c` on `ℕ` where `c.Rel i j` implies `i` and `j` have
different parity). We calculate the homology of these periodic complexes.

In particular, we show `... ⟶ X --𝟙--> X --0--> X --𝟙--> X --0--> X ⟶ 0` is homotopy equivalent
to the single complex where `X` is in degree `0`.

-/

@[expose] public section
universe v u

open CategoryTheory Limits

namespace ComplexShape

/-
**ComplexShape.up_nat_odd_add** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape`。
形式化陈述：up_nat_odd_add {i j : Nat} (h : (ComplexShape.up Nat).Rel i j) : Odd (i + 
j)
参数：h : (ComplexShape.up Nat).Rel i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma up_nat_odd_add {i j : ℕ} (h : (ComplexShape.up ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num
/-
**ComplexShape.down_nat_odd_add** 是 Mathlib 中的一个引理，位于命名空间 `ComplexShape`。
形式化陈述：down_nat_odd_add {i j : Nat} (h : (ComplexShape.down Nat).Rel i j) : Odd (
i + j)
参数：h : (ComplexShape.down Nat).Rel i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma down_nat_odd_add {i j : ℕ} (h : (ComplexShape.down ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

end ComplexShape

namespace HomologicalComplex

open ShortComplex

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
  (A : C) {φ : A ⟶ A} {ψ : A ⟶ A} (hOdd : φ ≫ ψ = 0) (hEven : ψ ≫ φ = 0)

/-- Let `c : ComplexShape ℕ` be such that `i j : ℕ` have opposite parity if they are related by
`c`. Let `φ, ψ : A ⟶ A` be such that `φ ∘ ψ = ψ ∘ φ = 0`. This is a complex of shape `c` whose
objects are all `A`. For all `i, j` related by `c`, `dᵢⱼ = φ` when `i` is even, and `dᵢⱼ = ψ` when
`i` is odd. -/
@[simps!]
/-
**HomologicalComplex.alternatingConst** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComp
lex`。
形式化陈述：alternatingConst {c : ComplexShape Nat} [DecidableRel c.Rel] (hc : forall 
i j, c.Rel i j -> Odd (i + j)) : HomologicalComplex C c where X n
参数：hc : forall i j, c.Rel i j -> Odd (i + j)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `c : ComplexShape ℕ` be such that `i j : ℕ` have opposite parity if they are
 related by
`c`. Let `φ, ψ : A ⟶ A` be such that `φ ∘ ψ = ψ ∘ φ = 0`. This is a complex of s
hape `c` whose
objects are all `A`. For all `i, j` related by `c`, `dᵢⱼ = φ` when `i` is even, 
and `dᵢⱼ = ψ` when
`i` is odd.
-/
noncomputable def alternatingConst {c : ComplexShape ℕ} [DecidableRel c.Rel]
    (hc : ∀ i j, c.Rel i j → Odd (i + j)) :
    HomologicalComplex C c where
  X n := A
  d i j :=
    if hij : c.Rel i j then
      if hi : Even i then φ
      else ψ
    else 0
  shape i j := by aesop
  d_comp_d' i j k hij hjk := by
    have := hc i j hij
    split_ifs with hi hj hj
    · exact False.elim <| Nat.not_odd_iff_even.2 hi <| by simp_all [Nat.odd_add]
    · assumption
    · assumption
    · exact False.elim <| hj <| by simp_all [Nat.odd_add]

variable {c : ComplexShape ℕ} [DecidableRel c.Rel] (hc : ∀ i j, c.Rel i j → Odd (i + j))

open HomologicalComplex hiding mk

set_option backward.isDefEq.respectTransparency false in
/-- The `i, j, k`th short complex associated to the alternating constant complex on `φ, ψ : A ⟶ A`
is `A --ψ--> A --φ--> A` when `i ~ j, j ~ k` and `j` is even. -/
/-
**HomologicalComplex.alternatingConstScIsoEven** 是 Mathlib 中的一个定义，位于命名空间 `Homolo
gicalComplex`。
形式化陈述：alternatingConstScIsoEven {i j k : Nat} (hij : c.Rel i j) (hjk : c.Rel j k
) (h : Even j) : (alternatingConst A hOdd hEven hc).sc' i j k ≅ ShortComplex.mk 
ψ φ hEven
参数：hij : c.Rel i j；hjk : c.Rel j k；h : Even j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i, j, k`th short complex associated to the alternating constant complex on 
`φ, ψ : A ⟶ A`
is `A --ψ--> A --φ--> A` when `i ~ j, j ~ k` and `j` is even.
-/
noncomputable def alternatingConstScIsoEven
    {i j k : ℕ} (hij : c.Rel i j) (hjk : c.Rel j k) (h : Even j) :
    (alternatingConst A hOdd hEven hc).sc' i j k ≅ ShortComplex.mk ψ φ hEven :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, right_eq_ite_iff]
      intro hi
      have := hc i j hij
      exact False.elim <| Nat.not_odd_iff_even.2 hi <| by simp_all [Nat.odd_add])
    (by simp_all [alternatingConst])

set_option backward.isDefEq.respectTransparency false in
/-- The `i, j, k`th short complex associated to the alternating constant complex on `φ, ψ : A ⟶ A`
is `A --φ--> A --ψ--> A` when `i ~ j, j ~ k` and `j` is even. -/
/-
**HomologicalComplex.alternatingConstScIsoOdd** 是 Mathlib 中的一个定义，位于命名空间 `Homolog
icalComplex`。
形式化陈述：alternatingConstScIsoOdd {i j k : Nat} (hij : c.Rel i j) (hjk : c.Rel j k)
 (h : Odd j) : (alternatingConst A hOdd hEven hc).sc' i j k ≅ ShortComplex.mk φ 
ψ hOdd
参数：hij : c.Rel i j；hjk : c.Rel j k；h : Odd j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i, j, k`th short complex associated to the alternating constant complex on 
`φ, ψ : A ⟶ A`
is `A --φ--> A --ψ--> A` when `i ~ j, j ~ k` and `j` is even.
-/
noncomputable def alternatingConstScIsoOdd
    {i j k : ℕ} (hij : c.Rel i j) (hjk : c.Rel j k) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).sc' i j k ≅ ShortComplex.mk φ ψ hOdd :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [alternatingConst, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, left_eq_ite_iff]
      intro hi
      have := hc i j hij
      exact False.elim <| Nat.not_even_iff_odd.2 h <| by simp_all [Nat.odd_add])
    (by simp_all [alternatingConst])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**HomologicalComplex.alternatingConst_iCycles_even_comp** 是 Mathlib 中的一个引理，位于命名空
间 `HomologicalComplex`。
形式化陈述：alternatingConst_iCycles_even_comp [CategoryWithHomology C] {j : Nat} (hpj
 : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) : (alternatingCon
st A hOdd hEven hc).iCycles j ≫ φ = 0
参数：hpj : c.Rel (c.prev j) j；hnj : c.Rel j (c.next j)；h : Even j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap_i_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.ShortComplex.iCycles_g`：iCycles_g : S.iCycles ≫ S.g = 0
-/
lemma alternatingConst_iCycles_even_comp [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (alternatingConst A hOdd hEven hc).iCycles j ≫ φ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScIsoEven,
    Category.id_comp (X := (alternatingConst A hOdd hEven hc).X _)]
    using (ShortComplex.mk ψ φ hEven).iCycles_g

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**HomologicalComplex.alternatingConst_iCycles_odd_comp** 是 Mathlib 中的一个引理，位于命名空间
 `HomologicalComplex`。
形式化陈述：alternatingConst_iCycles_odd_comp [CategoryWithHomology C] {j : Nat} (hpj 
: c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) : (alternatingConst
 A hOdd hEven hc).iCycles j ≫ ψ = 0
参数：hpj : c.Rel (c.prev j) j；hnj : c.Rel j (c.next j)；h : Odd j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap_i_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.ShortComplex.iCycles_g`：iCycles_g : S.iCycles ≫ S.g = 0
-/
lemma alternatingConst_iCycles_odd_comp [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).iCycles j ≫ ψ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, alternatingConstScIsoOdd,
    Category.id_comp (X := (alternatingConst A hOdd hEven hc).X _)]
    using (ShortComplex.mk φ ψ hOdd).iCycles_g

/-- The `j`th homology of the alternating constant complex on `φ, ψ : A ⟶ A` is the homology of
`A --ψ--> A --φ--> A` when `prev(j) ~ j, j ~ next(j)` and `j` is even. -/
/-
**HomologicalComplex.alternatingConstHomologyIsoEven** 是 Mathlib 中的一个定义，位于命名空间 `
HomologicalComplex`。
形式化陈述：alternatingConstHomologyIsoEven [CategoryWithHomology C] {j : Nat} (hpj : 
c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) : (alternatingConst 
A hOdd hEven hc).homology j ≅ (ShortComplex.mk ψ φ hEven).homology
参数：hpj : c.Rel (c.prev j) j；hnj : c.Rel j (c.next j)；h : Even j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `j`th homology of the alternating constant complex on `φ, ψ : A ⟶ A` is the 
homology of
`A --ψ--> A --φ--> A` when `prev(j) ~ j, j ~ next(j)` and `j` is even.
-/
noncomputable def alternatingConstHomologyIsoEven [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (alternatingConst A hOdd hEven hc).homology j ≅ (ShortComplex.mk ψ φ hEven).homology :=
  ShortComplex.homologyMapIso (alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)

/-- The `j`th homology of the alternating constant complex on `φ, ψ : A ⟶ A` is the homology of
`A --φ--> A --ψ--> A` when `prev(j) ~ j, j ~ next(j)` and `j` is odd. -/
/-
**HomologicalComplex.alternatingConstHomologyIsoOdd** 是 Mathlib 中的一个定义，位于命名空间 `H
omologicalComplex`。
形式化陈述：alternatingConstHomologyIsoOdd [CategoryWithHomology C] {j : Nat} (hpj : c
.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) : (alternatingConst A 
hOdd hEven hc).homology j ≅ (ShortComplex.mk φ ψ hOdd).homology
参数：hpj : c.Rel (c.prev j) j；hnj : c.Rel j (c.next j)；h : Odd j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `j`th homology of the alternating constant complex on `φ, ψ : A ⟶ A` is the 
homology of
`A --φ--> A --ψ--> A` when `prev(j) ~ j, j ~ next(j)` and `j` is odd.
-/
noncomputable def alternatingConstHomologyIsoOdd [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (alternatingConst A hOdd hEven hc).homology j ≅ (ShortComplex.mk φ ψ hOdd).homology :=
  ShortComplex.homologyMapIso (alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)

end HomologicalComplex

open CategoryTheory Limits AlgebraicTopology

variable {C : Type*} [Category* C]

namespace ChainComplex

set_option backward.defeqAttrib.useBackward true in
/-- The chain complex `X ←0- X ←𝟙- X ←0- X ←𝟙- X ⋯`.
It is exact away from `0` and has homology `X` at `0`. -/
@[simps]
/-
**ChainComplex.alternatingConst** 是 Mathlib 中的一个定义，位于命名空间 `ChainComplex`。
形式化陈述：alternatingConst [HasZeroMorphisms C] : C ⥤ ChainComplex C Nat where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ComplexShape.down_nat_odd_add`：down_nat_odd_add {i j : Nat} (h : (Comple
xShape.down Nat).Rel i j) : Odd (i + j)

--- 原说明 ---
The chain complex `X ←0- X ←𝟙- X ←0- X ←𝟙- X ⋯`.
It is exact away from `0` and has homology `X` at `0`.
-/
noncomputable def alternatingConst [HasZeroMorphisms C] : C ⥤ ChainComplex C ℕ where
  obj X := HomologicalComplex.alternatingConst X (Category.id_comp 0) (Category.comp_id 0)
    (fun _ _ => ComplexShape.down_nat_odd_add)
  map {X Y} f := {
    f _ := f
    comm' i j hij := by by_cases Even i <;> simp_all [-Nat.not_even_iff_odd] }

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `n`-th homology of the alternating constant complex is zero for non-zero even `n`. -/
noncomputable
/-
**ChainComplex.alternatingConstHomologyDataEvenNEZero** 是 Mathlib 中的一个定义，位于命名空间 
`ChainComplex`。
形式化陈述：alternatingConstHomologyDataEvenNEZero (X : C) (n : Nat) (hn : Even n) (h₀
 : n != 0) : ((alternatingConst.obj X).sc n).HomologyData
参数：X : C；n : Nat；hn : Even n；h₀ : n != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def alternatingConstHomologyDataEvenNEZero (X : C) (n : ℕ) (hn : Even n) (h₀ : n ≠ 0) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofIsLimitKernelFork _ (by simp [Nat.even_add_one, hn]) _
    (Limits.zeroKernelOfCancelZero _ (by cases n <;> simp_all))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `n`-th homology of the alternating constant complex is zero for odd `n`. -/
noncomputable
/-
**ChainComplex.alternatingConstHomologyDataOdd** 是 Mathlib 中的一个定义，位于命名空间 `ChainC
omplex`。
形式化陈述：alternatingConstHomologyDataOdd (X : C) (n : Nat) (hn : Odd n) : ((alterna
tingConst.obj X).sc n).HomologyData
参数：X : C；n : Nat；hn : Odd n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def alternatingConstHomologyDataOdd (X : C) (n : ℕ) (hn : Odd n) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofIsColimitCokernelCofork _ (by simp [hn]) _ (Limits.zeroCokernelOfZeroCancel _ (by simp [hn]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
/-
**ChainComplex.alternatingConstHomologyDataZero** 是 Mathlib 中的一个定义，位于命名空间 `Chain
Complex`。
形式化陈述：alternatingConstHomologyDataZero (X : C) (n : Nat) (hn : n = 0) : ((altern
atingConst.obj X).sc n).HomologyData
参数：X : C；n : Nat；hn : n = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def alternatingConstHomologyDataZero (X : C) (n : ℕ) (hn : n = 0) :
    ((alternatingConst.obj X).sc n).HomologyData :=
  .ofZeros _ (by simp [hn]) (by simp [hn])
/-
**ChainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `ChainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) (n : ℕ) : (alternatingConst.obj X).HasHomology n := by
  rcases n.even_or_odd with h | h
  · rcases n with - | n
    · exact ⟨⟨alternatingConstHomologyDataZero X _ rfl⟩⟩
    · exact ⟨⟨alternatingConstHomologyDataEvenNEZero X _ h (by simp)⟩⟩
  · exact ⟨⟨alternatingConstHomologyDataOdd X _ h⟩⟩

/-- The `n`-th homology of the alternating constant complex is `X` for `n ≠ 0`. -/
/-
**ChainComplex.alternatingConst_exactAt** 是 Mathlib 中的一个引理，位于命名空间 `ChainComplex`
。
形式化陈述：alternatingConst_exactAt (X : C) (n : Nat) (hn : n != 0) : (alternatingCon
st.obj X).ExactAt n
参数：X : C；n : Nat；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)

--- 原说明 ---
The `n`-th homology of the alternating constant complex is `X` for `n ≠ 0`.
-/
lemma alternatingConst_exactAt (X : C) (n : ℕ) (hn : n ≠ 0) :
    (alternatingConst.obj X).ExactAt n := by
  rcases n.even_or_odd with h | h
  · exact ⟨(alternatingConstHomologyDataEvenNEZero X _ h hn), isZero_zero C⟩
  · exact ⟨(alternatingConstHomologyDataOdd X _ h), isZero_zero C⟩

/-- The `n`-th homology of the alternating constant complex is `X` for `n = 0`. -/
noncomputable
/-
**ChainComplex.alternatingConstHomologyZero** 是 Mathlib 中的一个定义，位于命名空间 `ChainComp
lex`。
形式化陈述：alternatingConstHomologyZero (X : C) : (alternatingConst.obj X).homology 0
 ≅ X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def alternatingConstHomologyZero (X : C) : (alternatingConst.obj X).homology 0 ≅ X :=
  (alternatingConstHomologyDataZero X _ rfl).left.homologyIso

end ChainComplex

variable [Preadditive C] [HasZeroObject C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The alternating face complex of the constant complex is the alternating constant complex. -/
/-
**AlgebraicTopology.alternatingFaceMapComplexConst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgebraicTopology.alternatingFaceMapComplexConst : Functor.const _ ⋙ alter
natingFaceMapComplex C ≅ ChainComplex.alternatingConst
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The alternating face complex of the constant complex is the alternating constant
 complex.
-/
noncomputable def AlgebraicTopology.alternatingFaceMapComplexConst :
    Functor.const _ ⋙ alternatingFaceMapComplex C ≅ ChainComplex.alternatingConst :=
  NatIso.ofComponents (fun X ↦ HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) <| by
    rintro _ i rfl
    simp [SimplicialObject.δ, ← Finset.sum_smul, Fin.sum_neg_one_pow, Nat.even_add_one,
      -Nat.not_even_iff_odd]) (by intros; ext; simp)

namespace ChainComplex

/-- `alternatingConst.obj X` is homotopy equivalent to the chain
complex `(single₀ C).obj X`. -/
/-
**ChainComplex.alternatingConstHomotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ChainCom
plex`。
形式化陈述：alternatingConstHomotopyEquiv (X : C) : HomotopyEquiv (alternatingConst.ob
j X) ((single₀ C).obj X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`alternatingConst.obj X` is homotopy equivalent to the chain
complex `(single₀ C).obj X`.
-/
noncomputable def alternatingConstHomotopyEquiv (X : C) :
    HomotopyEquiv (alternatingConst.obj X) ((single₀ C).obj X) :=
  (HomotopyEquiv.ofIso (alternatingFaceMapComplexConst.app X).symm).trans
    ((SimplicialObject.Augmented.ExtraDegeneracy.const X).homotopyEquiv)

end ChainComplex

