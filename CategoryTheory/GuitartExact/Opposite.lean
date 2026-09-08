/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.VerticalComposition

/-!
# The opposite of a Guitart exact square

A `2`-square is Guitart exact iff the opposite (transposed) `2`-square
is Guitart exact.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}

namespace TwoSquare

variable (w : TwoSquare T L R B)

section

variable {X₃ : C₃ᵒᵖ} {X₂ : C₂ᵒᵖ} (g : B.op.obj X₃ ⟶ R.op.obj X₂)

namespace structuredArrowRightwardsOpEquivalence

/-- Auxiliary definition for `structuredArrowRightwardsOpEquivalence`. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.structuredArrowRightwardsOpEquivalence.functor** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.TwoSquare.structuredArrowRightwardsOpEquival
ence`。
形式化陈述：functor : (w.op.StructuredArrowRightwards g)ᵒᵖ ⥤ w.CostructuredArrowDownwa
rds g.unop where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `structuredArrowRightwardsOpEquivalence`.
-/
def functor :
    (w.op.StructuredArrowRightwards g)ᵒᵖ ⥤
      w.CostructuredArrowDownwards g.unop where
  obj f := CostructuredArrowDownwards.mk _ _ f.unop.right.left.unop
      f.unop.right.hom.unop f.unop.hom.left.unop
      (Quiver.Hom.op_inj (by simpa using! CostructuredArrow.w f.unop.hom))
  map {f f'} φ :=
    CostructuredArrow.homMk
      (StructuredArrow.homMk (φ.unop.right.left.unop)
        (Quiver.Hom.op_inj (CostructuredArrow.w φ.unop.right))) (by
          ext
          exact Quiver.Hom.op_inj
            ((CostructuredArrow.proj _ _).congr_map (StructuredArrow.w φ.unop)))

/-- Auxiliary definition for `structuredArrowRightwardsOpEquivalence`. -/
/-
**CategoryTheory.TwoSquare.structuredArrowRightwardsOpEquivalence.inverse** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.TwoSquare.structuredArrowRightwardsOpEquival
ence`。
形式化陈述：inverse : w.CostructuredArrowDownwards g.unop ⥤ (w.op.StructuredArrowRight
wards g)ᵒᵖ where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `structuredArrowRightwardsOpEquivalence`.
-/
def inverse :
    w.CostructuredArrowDownwards g.unop ⥤
      (w.op.StructuredArrowRightwards g)ᵒᵖ where
  obj f := Opposite.op
    (StructuredArrowRightwards.mk _ _ (Opposite.op f.left.right)
      f.hom.right.op f.left.hom.op (Quiver.Hom.unop_inj (StructuredArrow.w f.hom)))
  map {f f'} φ :=
    (StructuredArrow.homMk
      (CostructuredArrow.homMk (φ.left.right.op)
        (Quiver.Hom.unop_inj (by exact StructuredArrow.w φ.left)))
          (by
            ext
            exact Quiver.Hom.unop_inj
              ((StructuredArrow.proj _ _).congr_map (CostructuredArrow.w φ)))).op

end structuredArrowRightwardsOpEquivalence

set_option backward.isDefEq.respectTransparency false in
/-- If `w : TwoSquare T L R B`, and `g : B.op.obj X₃ ⟶ R.op.obj X₂`, this is
the obvious equivalence of categories between
`(w.op.StructuredArrowRightwards g)ᵒᵖ` and `w.CostructuredArrowDownwards g.unop`. -/
@[simps]
/-
**CategoryTheory.TwoSquare.structuredArrowRightwardsOpEquivalence** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.TwoSquare`。
形式化陈述：structuredArrowRightwardsOpEquivalence : (w.op.StructuredArrowRightwards g
)ᵒᵖ ≌ w.CostructuredArrowDownwards g.unop where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `w : TwoSquare T L R B`, and `g : B.op.obj X₃ ⟶ R.op.obj X₂`, this is
the obvious equivalence of categories between
`(w.op.StructuredArrowRightwards g)ᵒᵖ` and `w.CostructuredArrowDownwards g.unop`
.
-/
def structuredArrowRightwardsOpEquivalence :
    (w.op.StructuredArrowRightwards g)ᵒᵖ ≌
      w.CostructuredArrowDownwards g.unop where
  functor := structuredArrowRightwardsOpEquivalence.functor w g
  inverse := structuredArrowRightwardsOpEquivalence.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

/-
**CategoryTheory.TwoSquare.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.TwoSquare`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [w.GuitartExact] : w.op.GuitartExact := by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₃ X₂ g
  rw [← isConnected_op_iff_isConnected,
    isConnected_iff_of_equivalence (w.structuredArrowRightwardsOpEquivalence g)]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.TwoSquare.guitartExact_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.TwoSquare`。
形式化陈述：guitartExact_op_iff : w.op.GuitartExact ↔ w.GuitartExact
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.ext`：ext (w w' : TwoSquare T L R B) (h : forall
 (X : C₁), w.natTrans.app X = w'.natTrans.app X) : w = w'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.TwoSquare.vComp_app`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ 
: Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1
 : CategoryTheory.Catego…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.TwoSquare.guitartExact_of_isEquivalence_of_isIso`：∀ {C₁ :
 Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.instIsEquivalenceOppositeOpOp`：∀ (C : Type u₁) [inst : Ca
tegoryTheory.Category.{v₁, u₁} C], (CategoryTheory.opOp C).IsEquivalence
· 使用定理 `CategoryTheory.TwoSquare.instGuitartExactOppositeOp`：∀ {C₁ : Type u₁} {C
₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, 
u₁} C₁]   [inst_1 : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.instIsEquivalenceOppositeUnopUnop`：∀ (C : Type u₁) [inst 
: CategoryTheory.Category.{v₁, u₁} C], (CategoryTheory.unopUnop C).IsEquivalence
-/
lemma guitartExact_op_iff : w.op.GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro
    let w₁ : TwoSquare T (opOp C₁) (opOp C₂) T.op.op := 𝟙 _
    let w₂ : TwoSquare B.op.op (unopUnop C₃) (unopUnop C₄) B := 𝟙 _
    have : w = (w₁ ≫ᵥ w.op.op) ≫ᵥ w₂ := by cat_disch
    rw [this]
    infer_instance
  · intro
    infer_instance
/-
**CategoryTheory.TwoSquare.guitartExact_id'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.TwoSquare`。
形式化陈述：guitartExact_id' (F : C₁ ⥤ C₂) : GuitartExact (TwoSquare.mk F (𝟭 C₁) (𝟭 C₂
) F (𝟙 F))
参数：F : C₁ ⥤ C₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_op_iff`：guitartExact_op_iff : w.op
.GuitartExact ↔ w.GuitartExact
-/
instance guitartExact_id' (F : C₁ ⥤ C₂) :
    GuitartExact (TwoSquare.mk F (𝟭 C₁) (𝟭 C₂) F (𝟙 F)) := by
  rw [← guitartExact_op_iff]
  apply guitartExact_id
/-
**CategoryTheory.TwoSquare.guitartExact_of_isEquivalence_of_isIso'** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.TwoSquare`。
形式化陈述：guitartExact_of_isEquivalence_of_isIso' [T.IsEquivalence] [B.IsEquivalence
] [IsIso w.natTrans] : GuitartExact w
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_op_iff`：guitartExact_op_iff : w.op
.GuitartExact ↔ w.GuitartExact
· 使用定理 `CategoryTheory.TwoSquare.guitartExact_of_isEquivalence_of_isIso`：∀ {C₁ :
 Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Functor.instIsEquivalenceOppositeOp`：∀ (C : Type u₁) [ins
t : CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.TwoSquare.instIsIsoFunctorOppositeNatTransOp`：∀ {C₁ : Typ
e u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Catego…
-/
instance guitartExact_of_isEquivalence_of_isIso'
    [T.IsEquivalence] [B.IsEquivalence] [IsIso w.natTrans] : GuitartExact w := by
  rw [← guitartExact_op_iff]
  infer_instance

end TwoSquare

end CategoryTheory

