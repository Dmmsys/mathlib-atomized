/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# The (naive) shift on the opposite category

If `C` is a category equipped with a shift by a monoid `A`, the opposite category
can be equipped with a shift such that the shift functor by `n` is `(shiftFunctor C n).op`.
This is the "naive" opposite shift, which we shall set on a category `OppositeShift C A`,
which is a type synonym for `Cᵒᵖ`.

However, for the application to (pre)triangulated categories, we would like to
define the shift on `Cᵒᵖ` so that `shiftFunctor Cᵒᵖ n` for `n : ℤ` identifies to
`(shiftFunctor C (-n)).op` rather than `(shiftFunctor C n).op`. Then, the construction
of the shift on `Cᵒᵖ` shall combine the shift on `OppositeShift C A` and another
construction of the "pullback" of a shift by a monoid morphism like `n ↦ -n`.

If `F : C ⥤ D` is a functor between categories equipped with shifts by `A`, we define
a type synonym `OppositeShift.functor A F` for `F.op`. When `F` has a `CommShift` structure
by `A`, we define a `CommShift` structure by `A` on `OppositeShift.functor A F`. In this
way, we can make this an instance and reserve `F.op` for the `CommShift` instance by
the modified shift in the case of (pre)triangulated categories.

Similarly, if `τ` is a natural transformation between functors `F,G : C ⥤ D`, we define
a type synonym for `τ.op` called
`OppositeShift.natTrans A τ : OppositeShift.functor A F ⟶ OppositeShift.functor A G`.
When `τ` has a `CommShift` structure by `A` (i.e. is compatible with `CommShift` structures
on `F` and `G`), we define a `CommShift` structure by `A` on `OppositeShift.natTrans A τ`.

Finally, if we have an adjunction `F ⊣ G` (with `G : D ⥤ C`), we define a type synonym
`OppositeShift.adjunction A adj : OppositeShift.functor A G ⊣ OppositeShift.functor A F`
for `adj.op`, and we show that, if `adj` compatible with `CommShift` structures
on `F` and `G`, then `OppositeShift.adjunction A adj` is also compatible with the pulled back
`CommShift` structures.

Given a `CommShift` structure on a functor `F`, we define a `CommShift` structure on `F.op`
(and vice versa).
We also prove that, if an adjunction `F ⊣ G` is compatible with `CommShift` structures on
`F` and `G`, then the opposite adjunction `G.op ⊣ F.op` is compatible with the opposite
`CommShift` structures.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category

section

variable (C : Type*) [Category* C] (A : Type*) [AddMonoid A] [HasShift C A]

namespace HasShift

set_option backward.defeqAttrib.useBackward true in
/-- Construction of the naive shift on the opposite category of a category `C`:
the shiftfunctor by `n` is `(shiftFunctor C n).op`. -/
/-
**CategoryTheory.HasShift.mkShiftCoreOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.HasShift`。
形式化陈述：mkShiftCoreOp : ShiftMkCore Cᵒᵖ A where F n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construction of the naive shift on the opposite category of a category `C`:
the shiftfunctor by `n` is `(shiftFunctor C n).op`.
-/
def mkShiftCoreOp : ShiftMkCore Cᵒᵖ A where
  F n := (shiftFunctor C n).op
  zero := (NatIso.op (shiftFunctorZero C A)).symm
  add a b := (NatIso.op (shiftFunctorAdd C a b)).symm
  assoc_hom_app m₁ m₂ m₃ X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_assoc_inv_app m₁ m₂ m₃ X.unop).trans
      (by simp [shiftFunctorAdd']))
  zero_add_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_zero_add_inv_app n X.unop).trans (by simp))
  add_zero_hom_app n X :=
    Quiver.Hom.unop_inj ((shiftFunctorAdd_add_zero_inv_app n X.unop).trans (by simp))

end HasShift

/-- The category `OppositeShift C A` is the opposite category `Cᵒᵖ` equipped
with the naive shift: `shiftFunctor (OppositeShift C A) n` is `(shiftFunctor C n).op`. -/
@[nolint unusedArguments]
/-
**CategoryTheory.OppositeShift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：OppositeShift (A : Type*) [AddMonoid A] [HasShift C A]
参数：A : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category `OppositeShift C A` is the opposite category `Cᵒᵖ` equipped
with the naive shift: `shiftFunctor (OppositeShift C A) n` is `(shiftFunctor C n
).op`.
-/
def OppositeShift (A : Type*) [AddMonoid A] [HasShift C A] := Cᵒᵖ
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (OppositeShift C A) := inferInstanceAs (Category Cᵒᵖ)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasShift (OppositeShift C A) A :=
  hasShiftMk Cᵒᵖ A (HasShift.mkShiftCoreOp C A)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] : HasZeroObject (OppositeShift C A) := by
  dsimp only [OppositeShift]
  infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] : Preadditive (OppositeShift C A) :=
  inferInstanceAs (Preadditive Cᵒᵖ)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive C] (n : A) [(shiftFunctor C n).Additive] :
    (shiftFunctor (OppositeShift C A) n).Additive := by
  change (shiftFunctor C n).op.Additive
  infer_instance
/-
**CategoryTheory.oppositeShiftFunctorZero_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：oppositeShiftFunctorZero_inv_app (X : OppositeShift C A) : (shiftFunctorZe
ro (OppositeShift C A) A).inv.app X = ((shiftFunctorZero C A).hom.app X.unop).op
参数：X : OppositeShift C A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma oppositeShiftFunctorZero_inv_app (X : OppositeShift C A) :
    (shiftFunctorZero (OppositeShift C A) A).inv.app X =
      ((shiftFunctorZero C A).hom.app X.unop).op := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.oppositeShiftFunctorZero_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：oppositeShiftFunctorZero_hom_app (X : OppositeShift C A) : (shiftFunctorZe
ro (OppositeShift C A) A).hom.app X = ((shiftFunctorZero C A).inv.app X.unop).op
参数：X : OppositeShift C A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.oppositeShiftFunctorZero_inv_app`：oppositeShiftFunctorZer
o_inv_app (X : OppositeShift C A) : (shiftFunctorZero (OppositeShift C A) A).inv
.app X = ((shiftFunctorZero C A).hom.…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.op_id`：op_id {X : C} : (𝟙 X).op = 𝟙 (op X)
-/
lemma oppositeShiftFunctorZero_hom_app (X : OppositeShift C A) :
    (shiftFunctorZero (OppositeShift C A) A).hom.app X =
      ((shiftFunctorZero C A).inv.app X.unop).op := by
  rw [← cancel_mono ((shiftFunctorZero (OppositeShift C A) A).inv.app X),
    Iso.hom_inv_id_app, oppositeShiftFunctorZero_inv_app, ← op_comp,
    Iso.hom_inv_id_app, op_id]
  rfl

variable {C A}
variable (X : OppositeShift C A) (a b c : A) (h : a + b = c)
/-
**CategoryTheory.oppositeShiftFunctorAdd_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory`。
形式化陈述：oppositeShiftFunctorAdd_inv_app : (shiftFunctorAdd (OppositeShift C A) a b
).inv.app X = ((shiftFunctorAdd C a b).hom.app X.unop).op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma oppositeShiftFunctorAdd_inv_app :
    (shiftFunctorAdd (OppositeShift C A) a b).inv.app X =
      ((shiftFunctorAdd C a b).hom.app X.unop).op := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.oppositeShiftFunctorAdd_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory`。
形式化陈述：oppositeShiftFunctorAdd_hom_app : (shiftFunctorAdd (OppositeShift C A) a b
).hom.app X = ((shiftFunctorAdd C a b).inv.app X.unop).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.oppositeShiftFunctorAdd_inv_app`：oppositeShiftFunctorAdd_
inv_app : (shiftFunctorAdd (OppositeShift C A) a b).inv.app X = ((shiftFunctorAd
d C a b).hom.app X.unop).op
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.op_id`：op_id {X : C} : (𝟙 X).op = 𝟙 (op X)
-/
lemma oppositeShiftFunctorAdd_hom_app :
    (shiftFunctorAdd (OppositeShift C A) a b).hom.app X =
      ((shiftFunctorAdd C a b).inv.app X.unop).op := by
  rw [← cancel_mono ((shiftFunctorAdd (OppositeShift C A) a b).inv.app X),
    Iso.hom_inv_id_app, oppositeShiftFunctorAdd_inv_app, ← op_comp,
    Iso.hom_inv_id_app, op_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.oppositeShiftFunctorAdd'_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {A : Type u
_2} [inst_1 : AddMonoid A]   [inst_2 : CategoryTheory.HasShift C A] (X : Categor
yTheory.OppositeShift C A) (a b c : A) (h : a + b = c),   (CategoryTheory.shiftF
unctorAdd' (CategoryTheory.OppositeShift C A) a b c h).inv.app X =     ((Categor
yTheory.shiftFunctorAdd' C a b c h).hom.app (Opposite.unop X)).op
参数：X : CategoryTheory.OppositeShift C A；a b c : A；h : a + b = c；CategoryTheory.s
hiftFunctorAdd' (CategoryTheory.OppositeShift C A) a b c h；(CategoryTheory.shift
FunctorAdd' C a b c h).hom.app (Opposite.unop X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma oppositeShiftFunctorAdd'_inv_app :
    (shiftFunctorAdd' (OppositeShift C A) a b c h).inv.app X =
      ((shiftFunctorAdd' C a b c h).hom.app X.unop).op := by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_inv_app]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.oppositeShiftFunctorAdd'_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {A : Type u
_2} [inst_1 : AddMonoid A]   [inst_2 : CategoryTheory.HasShift C A] (X : Categor
yTheory.OppositeShift C A) (a b c : A) (h : a + b = c),   (CategoryTheory.shiftF
unctorAdd' (CategoryTheory.OppositeShift C A) a b c h).hom.app X =     ((Categor
yTheory.shiftFunctorAdd' C a b c h).inv.app (Opposite.unop X)).op
参数：X : CategoryTheory.OppositeShift C A；a b c : A；h : a + b = c；CategoryTheory.s
hiftFunctorAdd' (CategoryTheory.OppositeShift C A) a b c h；(CategoryTheory.shift
FunctorAdd' C a b c h).inv.app (Opposite.unop X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用引理 `CategoryTheory.oppositeShiftFunctorAdd_hom_app`：oppositeShiftFunctorAdd_
hom_app : (shiftFunctorAdd (OppositeShift C A) a b).hom.app X = ((shiftFunctorAd
d C a b).inv.app X.unop).op
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma oppositeShiftFunctorAdd'_hom_app :
    (shiftFunctorAdd' (OppositeShift C A) a b c h).hom.app X =
      ((shiftFunctorAdd' C a b c h).inv.app X.unop).op := by
  subst h
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, oppositeShiftFunctorAdd_hom_app]

end

variable {C D : Type*} [Category* C] [Category* D] (A : Type*) [AddMonoid A]
  [HasShift C A] [HasShift D A] (F : C ⥤ D)

/--
The functor `F.op`, seen as a functor from `OppositeShift C A` to `OppositeShift D A`.
(We will use this to carry a `CommShift` instance for the naive shifts on the opposite category.
Then, in the pretriangulated case, we will be able to put a `CommShift` instance on `F.op`
for the modified shifts and not deal with instance clashes.)
-/
/-
**CategoryTheory.OppositeShift.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.OppositeShift`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         (A
 : Type u_3) →           [inst_2 : AddMonoid A] →             [inst_3 : Category
Theory.HasShift C A] →               [inst_4 : CategoryTheory.HasShift D A] →   
              CategoryTheory.Functor C D →                   CategoryTheory.Func
tor (CategoryTheory.OppositeShift C A) (CategoryTheory.OppositeShift D A)
参数：A : Type u_3；CategoryTheory.OppositeShift C A；CategoryTheory.OppositeShift D 
A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F.op`, seen as a functor from `OppositeShift C A` to `OppositeShift
 D A`.
(We will use this to carry a `CommShift` instance for the naive shifts on the op
posite category.
Then, in the pretriangulated case, we will be able to put a `CommShift` instance
 on `F.op`
for the modified shifts and not deal with instance clashes.)
-/
def OppositeShift.functor : OppositeShift C A ⥤ OppositeShift D A := F.op

variable {F} in
/--
The natural transformation `τ`, seen as a natural transformation from `OppositeShift.functor F A`
to `OppositeShift.functor G A`..
-/
/-
**CategoryTheory.OppositeShift.natTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.OppositeShift`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         (A
 : Type u_3) →           [inst_2 : AddMonoid A] →             [inst_3 : Category
Theory.HasShift C A] →               [inst_4 : CategoryTheory.HasShift D A] →   
              {F G : CategoryTheory.Functor C D} →                   (F ⟶ G) → (
CategoryTheory.OppositeShift.functor A G ⟶ CategoryTheory.OppositeShift.functor 
A F)
参数：A : Type u_3；F ⟶ G；CategoryTheory.OppositeShift.functor A G ⟶ CategoryTheory.
OppositeShift.functor A F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `τ`, seen as a natural transformation from `OppositeS
hift.functor F A`
to `OppositeShift.functor G A`..
-/
def OppositeShift.natTrans {G : C ⥤ D} (τ : F ⟶ G) :
    OppositeShift.functor A G ⟶ OppositeShift.functor A F :=
  NatTrans.op τ

namespace Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Given a `CommShift` structure on `F`, this is the corresponding `CommShift` structure on
`OppositeShift.functor F` (for the naive shifts on the opposite categories).
-/
/-
**CategoryTheory.Functor.commShiftOp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：commShiftOp [CommShift F A] : CommShift (OppositeShift.functor A F) A wher
e commShiftIso a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `CommShift` structure on `F`, this is the corresponding `CommShift` stru
cture on
`OppositeShift.functor F` (for the naive shifts on the opposite categories).
-/
instance commShiftOp [CommShift F A] :
    CommShift (OppositeShift.functor A F) A where
  commShiftIso a := (NatIso.op (F.commShiftIso a)).symm
  commShiftIso_zero := by
    rw [commShiftIso_zero]
    ext
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app,
      CommShift.isoZero_inv_app, op_comp, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_inv_app, oppositeShiftFunctorZero_hom_app]
    rfl
  commShiftIso_add a b := by
    rw [commShiftIso_add]
    ext
    simp only [op_obj, comp_obj, Iso.symm_hom, NatIso.op_inv, NatTrans.op_app,
      CommShift.isoAdd_inv_app, op_comp, Category.assoc, CommShift.isoAdd_hom_app]
    erw [oppositeShiftFunctorAdd_inv_app, oppositeShiftFunctorAdd_hom_app]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.commShiftOp_iso_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：commShiftOp_iso_eq [CommShift F A] (a : A) : (OppositeShift.functor A F).c
ommShiftIso a = (NatIso.op (F.commShiftIso a)).symm
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma commShiftOp_iso_eq [CommShift F A] (a : A) :
    (OppositeShift.functor A F).commShiftIso a = (NatIso.op (F.commShiftIso a)).symm := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Given a `CommShift` structure on `OppositeShift.functor F` (for the naive shifts on the opposite
categories), this is the corresponding `CommShift` structure on `F`.
-/
@[simps -isSimp, instance_reducible]
/-
**CategoryTheory.Functor.commShiftUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：commShiftUnop [CommShift (OppositeShift.functor A F) A] : CommShift F A wh
ere commShiftIso a
参数：OppositeShift.functor A F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `CommShift` structure on `OppositeShift.functor F` (for the naive shifts
 on the opposite
categories), this is the corresponding `CommShift` structure on `F`.
-/
def commShiftUnop
    [CommShift (OppositeShift.functor A F) A] : CommShift F A where
  commShiftIso a := NatIso.removeOp ((OppositeShift.functor A F).commShiftIso a).symm
  commShiftIso_zero := by
    rw [commShiftIso_zero]
    ext
    simp only [NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app,
      CommShift.isoZero_inv_app, unop_comp, CommShift.isoZero_hom_app]
    erw [oppositeShiftFunctorZero_hom_app, oppositeShiftFunctorZero_inv_app]
    rfl
  commShiftIso_add a b := by
    rw [commShiftIso_add]
    ext
    simp only [NatIso.removeOp_hom, Iso.symm_hom, NatTrans.removeOp_app,
      CommShift.isoAdd_inv_app, unop_comp, Category.assoc,
      CommShift.isoAdd_hom_app]
    erw [oppositeShiftFunctorAdd_hom_app, oppositeShiftFunctorAdd_inv_app]
    rfl

end Functor

namespace NatTrans

variable {F} {G : C ⥤ D} [F.CommShift A] [G.CommShift A]

open Opposite in
/-
**CategoryTheory.NatTrans.commShift_op** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：commShift_op (τ : F ⟶ G) [NatTrans.CommShift τ A] : NatTrans.CommShift (Op
positeShift.natTrans A τ) A where shift_comm _
参数：τ : F ⟶ G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Opposite.op_inj_iff`：op_inj_iff (x y : α) : op x = op y ↔ x = y
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
-/
instance commShift_op (τ : F ⟶ G) [NatTrans.CommShift τ A] :
    NatTrans.CommShift (OppositeShift.natTrans A τ) A where
  shift_comm _ := by
    ext
    rw [← cancel_mono (((OppositeShift.functor A F).commShiftIso _).inv.app _),
      ← cancel_epi (((OppositeShift.functor A G).commShiftIso _).inv.app _)]
    simp only [Functor.comp_obj, comp_app, Functor.whiskerRight_app, assoc,
      Iso.inv_hom_id_app_assoc, Functor.whiskerLeft_app, Iso.hom_inv_id_app, comp_id]
    exact (op_inj_iff _ _).mpr (NatTrans.shift_app_comm τ _ (unop _))

end NatTrans

namespace NatTrans

variable (C) in
/-- The obvious isomorphism between the identity of `OppositeShift C A` and
`OppositeShift.functor (𝟙 C)`.
-/
/-
**CategoryTheory.NatTrans.OppositeShift.natIsoId** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.NatTrans.OppositeShift`。
形式化陈述：(C : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     (A 
: Type u_3) →       [inst_1 : AddMonoid A] →         [inst_2 : CategoryTheory.Ha
sShift C A] →           CategoryTheory.Functor.id (CategoryTheory.OppositeShift 
C A) ≅             CategoryTheory.OppositeShift.functor A (CategoryTheory.Functo
r.id C)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious isomorphism between the identity of `OppositeShift C A` and
`OppositeShift.functor (𝟙 C)`.
-/
def OppositeShift.natIsoId : 𝟭 (OppositeShift C A) ≅ OppositeShift.functor A (𝟭 C) := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The natural isomorphism `NatTrans.OppositeShift.natIsoId C A` commutes with shifts.
-/
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `NatTrans.OppositeShift.natIsoId C A` commutes with shif
ts.
-/
instance : NatTrans.CommShift (OppositeShift.natIsoId C A).hom A where
  shift_comm _ := by
    ext
    dsimp [OppositeShift.natIsoId, Functor.commShiftOp_iso_eq]
    simp only [Functor.commShiftIso_id_hom_app, Functor.map_id,
      comp_id, Functor.commShiftIso_id_inv_app, CategoryTheory.op_id, id_comp]
    rfl

variable {E : Type*} [Category* E] [HasShift E A] (G : D ⥤ E)

/-- The obvious isomorphism between `OppositeShift.functor (F ⋙ G)` and the
composition of `OppositeShift.functor F` and `OppositeShift.functor G`.
-/
/-
**CategoryTheory.NatTrans.OppositeShift.natIsoComp** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.NatTrans.OppositeShift`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         (A
 : Type u_3) →           [inst_2 : AddMonoid A] →             [inst_3 : Category
Theory.HasShift C A] →               [inst_4 : CategoryTheory.HasShift D A] →   
              (F : CategoryTheory.Functor C D) →                   {E : Type u_4
} →                     [inst_5 : CategoryTheory.Category.{v_3, u_4} E] →       
                [inst_6 : CategoryTheory.HasShift E A] →                        
 (G : CategoryTheory.Functor D E) →                           CategoryTheory.Opp
ositeShift.functor A (F.comp G) ≅                             (CategoryTheory.Op
positeShift.functor A F).comp (CategoryTheory.OppositeShift.functor A G)
参数：A : Type u_3；F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；F.
comp G；CategoryTheory.OppositeShift.functor A F；CategoryTheory.OppositeShift.fun
ctor A G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious isomorphism between `OppositeShift.functor (F ⋙ G)` and the
composition of `OppositeShift.functor F` and `OppositeShift.functor G`.
-/
def OppositeShift.natIsoComp : OppositeShift.functor A (F ⋙ G) ≅
    OppositeShift.functor A F ⋙ OppositeShift.functor A G := Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.CommShift A] [G.CommShift A] :
    NatTrans.CommShift (OppositeShift.natIsoComp A F G).hom A where
  shift_comm _ := by
    ext
    dsimp [OppositeShift.natIsoComp, Functor.commShiftOp_iso_eq]
    simp only [Functor.map_id, comp_id, id_comp]
    rfl

end NatTrans

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The adjunction `adj`, seen as an adjunction between `OppositeShift.functor G`
and `OppositeShift.functor F`.
-/
@[simps -isSimp]
/-
**CategoryTheory.OppositeShift.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.OppositeShift`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         (A
 : Type u_3) →           [inst_2 : AddMonoid A] →             [inst_3 : Category
Theory.HasShift C A] →               [inst_4 : CategoryTheory.HasShift D A] →   
              {F : CategoryTheory.Functor C D} →                   {G : Category
Theory.Functor D C} →                     (F ⊣ G) → (CategoryTheory.OppositeShif
t.functor A G ⊣ CategoryTheory.OppositeShift.functor A F)
参数：A : Type u_3；F ⊣ G；CategoryTheory.OppositeShift.functor A G ⊣ CategoryTheory.
OppositeShift.functor A F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `adj`, seen as an adjunction between `OppositeShift.functor G`
and `OppositeShift.functor F`.
-/
def OppositeShift.adjunction {F} {G : D ⥤ C} (adj : F ⊣ G) :
    OppositeShift.functor A G ⊣ OppositeShift.functor A F where
  unit := (NatTrans.OppositeShift.natIsoId D A).hom ≫
    OppositeShift.natTrans A adj.counit ≫ (NatTrans.OppositeShift.natIsoComp A G F).hom
  counit := (NatTrans.OppositeShift.natIsoComp A F G).inv ≫
    OppositeShift.natTrans A adj.unit ≫ (NatTrans.OppositeShift.natIsoId C A).inv
  left_triangle_components _ := by
    dsimp [OppositeShift.natTrans, NatTrans.OppositeShift.natIsoComp,
      NatTrans.OppositeShift.natIsoId, OppositeShift.functor]
    simp only [comp_id, id_comp, Quiver.Hom.unop_op]
    rw [← op_comp, adj.right_triangle_components]
    rfl
  right_triangle_components _ := by
    dsimp [OppositeShift.natTrans, NatTrans.OppositeShift.natIsoComp,
      NatTrans.OppositeShift.natIsoId, OppositeShift.functor]
    simp only [comp_id, id_comp, Quiver.Hom.unop_op]
    rw [← op_comp, adj.left_triangle_components]
    rfl

namespace Adjunction

variable {F} {G : D ⥤ C} (adj : F ⊣ G)

/--
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F` and `G`, then
the opposite adjunction `OppositeShift.adjunction adj` is compatible with the opposite
`CommShift` structures.
-/
/-
**CategoryTheory.Adjunction.commShift_op** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Adjunction`。
形式化陈述：commShift_op [F.CommShift A] [G.CommShift A] [adj.CommShift A] : Adjunctio
n.CommShift (OppositeShift.adjunction A adj) A where commShift_unit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.CommShift.comp`：∀ {C : Type u_1} {D : Type u_2} 
[inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categor
y.{v_2, u_2} D] {F₁ F₂ F₃ : …
· 使用定理 `CategoryTheory.NatTrans.instCommShiftOppositeShiftHomFunctorNatIsoId`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (A : Type u_3) [ins
t_1 : AddMonoid A]   [inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_counit`：∀ {C : Type u_1} {
D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} {F : Categor…
· 使用定理 `CategoryTheory.NatTrans.instCommShiftOppositeShiftHomFunctorNatIsoComp`：
∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] (A : Type u_…
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_unit`：∀ {C : Type u_1} {D 
: Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_2, u_2} D} {F : Categor…

--- 原说明 ---
If an adjunction `F ⊣ G` is compatible with `CommShift` structures on `F` and `G
`, then
the opposite adjunction `OppositeShift.adjunction adj` is compatible with the op
posite
`CommShift` structures.
-/
instance commShift_op [F.CommShift A] [G.CommShift A] [adj.CommShift A] :
    Adjunction.CommShift (OppositeShift.adjunction A adj) A where
  commShift_unit := by dsimp [OppositeShift.adjunction]; infer_instance
  commShift_counit := by dsimp [OppositeShift.adjunction]; infer_instance

end Adjunction

end CategoryTheory

