/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.PUnit

/-!
# Properties of comma categories relating to adjunctions

This file shows that for a functor `G : D ⥤ C` the data of an initial object in each
`StructuredArrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.

Specifically, `adjunctionOfStructuredArrowInitials` gives the left adjoint assuming the
appropriate initial objects exist, and `mkInitialOfLeftAdjoint` constructs the initial objects
provided a left adjoint.

The duals are also shown.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (G : D ⥤ C)

section OfInitials

variable [∀ A, HasInitial (StructuredArrow A G)]

attribute [local simp] eq_iff_true_of_subsingleton in
/-- Implementation: If each structured arrow category on `G` has an initial object, an equivalence
which is helpful for constructing a left adjoint to `G`.
-/
@[simps]
/-
**CategoryTheory.leftAdjointOfStructuredArrowInitialsAux** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory`。
形式化陈述：leftAdjointOfStructuredArrowInitialsAux (A : C) (B : D) : ((⊥_ StructuredA
rrow A G).right ⟶ B) ≃ (A ⟶ G.obj B) where toFun g
参数：A : C；B : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation: If each structured arrow category on `G` has an initial object, 
an equivalence
which is helpful for constructing a left adjoint to `G`.
-/
def leftAdjointOfStructuredArrowInitialsAux (A : C) (B : D) :
    ((⊥_ StructuredArrow A G).right ⟶ B) ≃ (A ⟶ G.obj B) where
  toFun g := (⊥_ StructuredArrow A G).hom ≫ G.map g
  invFun f := CommaMorphism.right (initial.to (StructuredArrow.mk f))
  left_inv g := by
    let B' : StructuredArrow A G := StructuredArrow.mk ((⊥_ StructuredArrow A G).hom ≫ G.map g)
    let g' : ⊥_ StructuredArrow A G ⟶ B' := StructuredArrow.homMk g rfl
    have : initial.to _ = g' := by cat_disch
    change CommaMorphism.right (initial.to B') = _
    rw [this]
    rfl
  right_inv f := by
    let B' : StructuredArrow A G := StructuredArrow.mk f
    apply (CommaMorphism.w (initial.to B')).symm.trans (Category.id_comp _)

/--
If each structured arrow category on `G` has an initial object, construct a left adjoint to `G`. It
is shown that it is a left adjoint in `adjunctionOfStructuredArrowInitials`.
-/
/-
**CategoryTheory.leftAdjointOfStructuredArrowInitials** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory`。
形式化陈述：leftAdjointOfStructuredArrowInitials : C ⥤ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If each structured arrow category on `G` has an initial object, construct a left
 adjoint to `G`. It
is shown that it is a left adjoint in `adjunctionOfStructuredArrowInitials`.
-/
def leftAdjointOfStructuredArrowInitials : C ⥤ D :=
  Adjunction.leftAdjointOfEquiv (leftAdjointOfStructuredArrowInitialsAux G) fun _ _ => by simp

/--
If each structured arrow category on `G` has an initial object, we have a constructed left adjoint
to `G`.
-/
/-
**CategoryTheory.adjunctionOfStructuredArrowInitials** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory`。
形式化陈述：adjunctionOfStructuredArrowInitials : leftAdjointOfStructuredArrowInitials
 G ⊣ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If each structured arrow category on `G` has an initial object, we have a constr
ucted left adjoint
to `G`.
-/
def adjunctionOfStructuredArrowInitials : leftAdjointOfStructuredArrowInitials G ⊣ G :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- If each structured arrow category on `G` has an initial object, `G` is a right adjoint. -/
/-
**CategoryTheory.isRightAdjointOfStructuredArrowInitials** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory`。
形式化陈述：isRightAdjointOfStructuredArrowInitials : G.IsRightAdjoint where exists_le
ftAdjoint
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If each structured arrow category on `G` has an initial object, `G` is a right a
djoint.
-/
lemma isRightAdjointOfStructuredArrowInitials : G.IsRightAdjoint where
  exists_leftAdjoint := ⟨_, ⟨adjunctionOfStructuredArrowInitials G⟩⟩

end OfInitials

section OfTerminals

variable [∀ A, HasTerminal (CostructuredArrow G A)]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] eq_iff_true_of_subsingleton in
/-- Implementation: If each costructured arrow category on `G` has a terminal object, an equivalence
which is helpful for constructing a right adjoint to `G`.
-/
@[simps]
/-
**CategoryTheory.rightAdjointOfCostructuredArrowTerminalsAux** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory`。
形式化陈述：rightAdjointOfCostructuredArrowTerminalsAux (B : D) (A : C) : (G.obj B ⟶ A
) ≃ (B ⟶ (⊤_ CostructuredArrow G A).left) where toFun g
参数：B : D；A : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation: If each costructured arrow category on `G` has a terminal object
, an equivalence
which is helpful for constructing a right adjoint to `G`.
-/
def rightAdjointOfCostructuredArrowTerminalsAux (B : D) (A : C) :
    (G.obj B ⟶ A) ≃ (B ⟶ (⊤_ CostructuredArrow G A).left) where
  toFun g := CommaMorphism.left (terminal.from (CostructuredArrow.mk g))
  invFun g := G.map g ≫ (⊤_ CostructuredArrow G A).hom
  left_inv := by cat_disch
  right_inv g := by
    let B' : CostructuredArrow G A :=
      CostructuredArrow.mk (G.map g ≫ (⊤_ CostructuredArrow G A).hom)
    let g' : B' ⟶ ⊤_ CostructuredArrow G A := CostructuredArrow.homMk g rfl
    have : terminal.from _ = g' := by cat_disch
    change CommaMorphism.left (terminal.from B') = _
    rw [this]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
If each costructured arrow category on `G` has a terminal object, construct a right adjoint to `G`.
It is shown that it is a right adjoint in `adjunctionOfCostructuredArrowTerminals`.
-/
/-
**CategoryTheory.rightAdjointOfCostructuredArrowTerminals** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory`。
形式化陈述：rightAdjointOfCostructuredArrowTerminals : C ⥤ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If each costructured arrow category on `G` has a terminal object, construct a ri
ght adjoint to `G`.
It is shown that it is a right adjoint in `adjunctionOfCostructuredArrowTerminal
s`.
-/
def rightAdjointOfCostructuredArrowTerminals : C ⥤ D :=
  Adjunction.rightAdjointOfEquiv (rightAdjointOfCostructuredArrowTerminalsAux G)
      fun B₁ B₂ A f g => by
    rw [← Equiv.eq_symm_apply]
    simp

/-- If each costructured arrow category on `G` has a terminal object, we have a constructed right
adjoint to `G`.
-/
/-
**CategoryTheory.adjunctionOfCostructuredArrowTerminals** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory`。
形式化陈述：adjunctionOfCostructuredArrowTerminals : G ⊣ rightAdjointOfCostructuredArr
owTerminals G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If each costructured arrow category on `G` has a terminal object, we have a cons
tructed right
adjoint to `G`.
-/
def adjunctionOfCostructuredArrowTerminals : G ⊣ rightAdjointOfCostructuredArrowTerminals G :=
  Adjunction.adjunctionOfEquivRight _ _

/-- If each costructured arrow category on `G` has a terminal object, `G` is a left adjoint. -/
/-
**CategoryTheory.isLeftAdjoint_of_costructuredArrowTerminals** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory`。
形式化陈述：isLeftAdjoint_of_costructuredArrowTerminals : G.IsLeftAdjoint where exists
_rightAdjoint
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If each costructured arrow category on `G` has a terminal object, `G` is a left 
adjoint.
-/
lemma isLeftAdjoint_of_costructuredArrowTerminals : G.IsLeftAdjoint where
  exists_rightAdjoint :=
    ⟨rightAdjointOfCostructuredArrowTerminals G, ⟨Adjunction.adjunctionOfEquivRight _ _⟩⟩

end OfTerminals

section

variable {F : C ⥤ D}

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

set_option backward.defeqAttrib.useBackward true in
/-- Given a left adjoint to `G`, we can construct an initial object in each structured arrow
category on `G`. -/
/-
**CategoryTheory.mkInitialOfLeftAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：mkInitialOfLeftAdjoint (h : F ⊣ G) (A : C) : IsInitial (StructuredArrow.mk
 (h.unit.app A) : StructuredArrow A G) where desc B
参数：h : F ⊣ G；A : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a left adjoint to `G`, we can construct an initial object in each structur
ed arrow
category on `G`.
-/
def mkInitialOfLeftAdjoint (h : F ⊣ G) (A : C) :
    IsInitial (StructuredArrow.mk (h.unit.app A) : StructuredArrow A G) where
  desc B := StructuredArrow.homMk ((h.homEquiv _ _).symm B.pt.hom)
  uniq s m _ := by
    apply StructuredArrow.ext
    simp [← StructuredArrow.w m]

set_option backward.defeqAttrib.useBackward true in
/-- Given a right adjoint to `F`, we can construct a terminal object in each costructured arrow
category on `F`. -/
/-
**CategoryTheory.mkTerminalOfRightAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：mkTerminalOfRightAdjoint (h : F ⊣ G) (A : D) : IsTerminal (CostructuredArr
ow.mk (h.counit.app A) : CostructuredArrow F A) where lift B
参数：h : F ⊣ G；A : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a right adjoint to `F`, we can construct a terminal object in each costruc
tured arrow
category on `F`.
-/
def mkTerminalOfRightAdjoint (h : F ⊣ G) (A : D) :
    IsTerminal (CostructuredArrow.mk (h.counit.app A) : CostructuredArrow F A) where
  lift B := CostructuredArrow.homMk (h.homEquiv _ _ B.pt.hom)
  uniq s m _ := by
    apply CostructuredArrow.ext
    simp [← CostructuredArrow.w m]

end

/-
**CategoryTheory.isRightAdjoint_iff_hasInitial_structuredArrow** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory`。
形式化陈述：isRightAdjoint_iff_hasInitial_structuredArrow {G : D ⥤ C} : G.IsRightAdjoi
nt ↔ forall A, HasInitial (StructuredArrow A G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hasInitial`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsInitial X),
   CategoryTheory.Limits.HasInit…
· 使用引理 `CategoryTheory.isRightAdjointOfStructuredArrowInitials`：isRightAdjointOf
StructuredArrowInitials : G.IsRightAdjoint where exists_leftAdjoint
-/
theorem isRightAdjoint_iff_hasInitial_structuredArrow {G : D ⥤ C} :
    G.IsRightAdjoint ↔ ∀ A, HasInitial (StructuredArrow A G) :=
  ⟨fun _ A => (mkInitialOfLeftAdjoint _ (Adjunction.ofIsRightAdjoint G) A).hasInitial,
    fun _ => isRightAdjointOfStructuredArrowInitials _⟩
/-
**CategoryTheory.isLeftAdjoint_iff_hasTerminal_costructuredArrow** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isLeftAdjoint_iff_hasTerminal_costructuredArrow {F : C ⥤ D} : F.IsLeftAdjo
int ↔ forall A, HasTerminal (CostructuredArrow F A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hasTerminal`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsTerminal 
X),   CategoryTheory.Limits.HasTer…
· 使用引理 `CategoryTheory.isLeftAdjoint_of_costructuredArrowTerminals`：isLeftAdjoin
t_of_costructuredArrowTerminals : G.IsLeftAdjoint where exists_rightAdjoint
-/
theorem isLeftAdjoint_iff_hasTerminal_costructuredArrow {F : C ⥤ D} :
    F.IsLeftAdjoint ↔ ∀ A, HasTerminal (CostructuredArrow F A) :=
  ⟨fun _ A => (mkTerminalOfRightAdjoint _ (Adjunction.ofIsLeftAdjoint F) A).hasTerminal,
    fun _ => isLeftAdjoint_of_costructuredArrowTerminals _⟩

end CategoryTheory

