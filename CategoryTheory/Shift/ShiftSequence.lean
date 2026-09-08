/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Sequences of functors from a category equipped with a shift

Let `F : C ⥤ A` be a functor from a category `C` that is equipped with a
shift by an additive monoid `M`. In this file, we define a typeclass
`F.ShiftSequence M` which includes the data of a sequence of functors
`F.shift a : C ⥤ A` for all `a : A`. For each `a : A`, we have
an isomorphism `F.isoShift a : shiftFunctor C a ⋙ F ≅ F.shift a` which
satisfies some coherence relations. This allows to state results
(e.g. the long exact sequence of a homology functor (TODO)) using
functors `F.shift a` rather than `shiftFunctor C a ⋙ F`. The reason
for this design is that we can often choose functors `F.shift a` that
have better definitional properties than `shiftFunctor C a ⋙ F`.
For example, if `C` is the derived category (TODO) of an abelian
category `A` and `F` is the homology functor in degree `0`, then
for any `n : ℤ`, we may choose `F.shift n` to be the homology functor
in degree `n`.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open CategoryTheory Category ZeroObject Limits

variable {C D A : Type*} [Category* C] [Category* D] [Category* A] (F : C ⥤ A)
  {π : C ⥤ D} {H : D ⥤ A} (e : π ⋙ H ≅ F)
  (M : Type*) [AddMonoid M] [HasShift C M] [HasShift D M]
  {G : Type*} [AddGroup G] [HasShift C G]

namespace CategoryTheory

namespace Functor

/-- A shift sequence for a functor `F : C ⥤ A` when `C` is equipped with a shift
by a monoid `M` involves a sequence of functor `sequence n : C ⥤ A` for all `n : M`
which behave like `shiftFunctor C n ⋙ F`. -/
/-
**CategoryTheory.Functor.ShiftSequence** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{C : Type u_1} →   {A : Type u_3} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_3, u_3} A] →         Ca
tegoryTheory.Functor C A →           (M : Type u_4) →             [inst_2 : AddM
onoid M] → [CategoryTheory.HasShift C M] → Type (max (max (max (max u_1 u_3) u_4
) v_1) v_3)
参数：M : Type u_4；max (max (max (max u_1 u_3) u_4) v_1) v_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shift sequence for a functor `F : C ⥤ A` when `C` is equipped with a shift
by a monoid `M` involves a sequence of functor `sequence n : C ⥤ A` for all `n :
 M`
which behave like `shiftFunctor C n ⋙ F`.
-/
class ShiftSequence where
  /-- a sequence of functors -/
  sequence : M → C ⥤ A
  /-- `sequence 0` identifies to the given functor -/
  isoZero : sequence 0 ≅ F
  /-- compatibility isomorphism with the shift -/
  shiftIso (n a a' : M) (ha' : n + a = a') : shiftFunctor C n ⋙ sequence a ≅ sequence a'
  shiftIso_zero (a : M) : shiftIso 0 a a (zero_add a) =
    isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _
  shiftIso_add : ∀ (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a''),
    shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (shiftIso n a a' ha') ≪≫ shiftIso m a' a'' ha''

set_option backward.defeqAttrib.useBackward true in
/-- The tautological shift sequence on a functor. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.ShiftSequence.tautological** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor.ShiftSequence`。
形式化陈述：{C : Type u_1} →   {A : Type u_3} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_3, u_3} A] →         (F
 : CategoryTheory.Functor C A) →           (M : Type u_4) → [inst_2 : AddMonoid 
M] → [inst_3 : CategoryTheory.HasShift C M] → F.ShiftSequence M
参数：F : CategoryTheory.Functor C A；M : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological shift sequence on a functor.
-/
noncomputable def ShiftSequence.tautological : ShiftSequence F M where
  sequence n := shiftFunctor C n ⋙ F
  isoZero := isoWhiskerRight (shiftFunctorZero C M) F ≪≫ F.leftUnitor
  shiftIso n a a' ha' := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftFunctorAdd' C n a a' ha').symm _
  shiftIso_zero a := by
    rw [shiftFunctorAdd'_zero_add]
    cat_disch
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    dsimp
    simp only [id_comp, ← Functor.map_comp]
    congr
    simpa only [← cancel_epi ((shiftFunctor C a).map ((shiftFunctorAdd C m n).hom.app X)),
      shiftFunctorAdd'_eq_shiftFunctorAdd, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, id_comp] using! shiftFunctorAdd'_assoc_inv_app m n a (m + n) a' a'' rfl ha'
        (by rw [← ha'', ← ha', add_assoc]) X

section

variable {M}
variable [F.ShiftSequence M]

/-- The shifted functors given by the shift sequence. -/
/-
**CategoryTheory.Functor.shift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：shift (n : M) : C ⥤ A
参数：n : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shifted functors given by the shift sequence.
-/
def shift (n : M) : C ⥤ A := ShiftSequence.sequence F n

/-- Compatibility isomorphism `shiftFunctor C n ⋙ F.shift a ≅ F.shift a'` when `n + a = a'`. -/
/-
**CategoryTheory.Functor.shiftIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：shiftIso (n a a' : M) (ha' : n + a = a') : shiftFunctor C n ⋙ F.shift a ≅ 
F.shift a'
参数：n a a' : M；ha' : n + a = a'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compatibility isomorphism `shiftFunctor C n ⋙ F.shift a ≅ F.shift a'` when `n + 
a = a'`.
-/
def shiftIso (n a a' : M) (ha' : n + a = a') :
    shiftFunctor C n ⋙ F.shift a ≅ F.shift a' :=
  ShiftSequence.shiftIso n a a' ha'

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.shiftIso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：shiftIso_hom_naturality {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶
 Y) : (shift F a).map (f⟦n⟧') ≫ (shiftIso F n a a' ha').hom.app Y = (shiftIso F 
n a a' ha').hom.app X ≫ (shift F a').map f
参数：n a a' : M；ha' : n + a = a'；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma shiftIso_hom_naturality {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y) :
    (shift F a).map (f⟦n⟧') ≫ (shiftIso F n a a' ha').hom.app Y =
      (shiftIso F n a a' ha').hom.app X ≫ (shift F a').map f :=
  (F.shiftIso n a a' ha').hom.naturality f

@[reassoc]
/-
**CategoryTheory.Functor.shiftIso_inv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：shiftIso_inv_naturality {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶
 Y) : (shift F a').map f ≫ (shiftIso F n a a' ha').inv.app Y = (shiftIso F n a a
' ha').inv.app X ≫ (shift F a).map (f⟦n⟧')
参数：n a a' : M；ha' : n + a = a'；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_inv_naturality {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y) :
    (shift F a').map f ≫ (shiftIso F n a a' ha').inv.app Y =
      (shiftIso F n a a' ha').inv.app X ≫ (shift F a).map (f⟦n⟧') := by
  simp

variable (M) in
/-- The canonical isomorphism `F.shift 0 ≅ F`. -/
/-
**CategoryTheory.Functor.isoShiftZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：isoShiftZero : F.shift (0 : M) ≅ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `F.shift 0 ≅ F`.
-/
def isoShiftZero : F.shift (0 : M) ≅ F := ShiftSequence.isoZero

/-- The canonical isomorphism `shiftFunctor C n ⋙ F ≅ F.shift n`. -/
/-
**CategoryTheory.Functor.isoShift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：isoShift (n : M) : shiftFunctor C n ⋙ F ≅ F.shift n
参数：n : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `shiftFunctor C n ⋙ F ≅ F.shift n`.
-/
def isoShift (n : M) : shiftFunctor C n ⋙ F ≅ F.shift n :=
  isoWhiskerLeft _ (F.isoShiftZero M).symm ≪≫ F.shiftIso _ _ _ (add_zero n)

@[reassoc]
/-
**CategoryTheory.Functor.isoShift_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：isoShift_hom_naturality (n : M) {X Y : C} (f : X ⟶ Y) : F.map (f⟦n⟧') ≫ (F
.isoShift n).hom.app Y = (F.isoShift n).hom.app X ≫ (F.shift n).map f
参数：n : M；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma isoShift_hom_naturality (n : M) {X Y : C} (f : X ⟶ Y) :
    F.map (f⟦n⟧') ≫ (F.isoShift n).hom.app Y =
      (F.isoShift n).hom.app X ≫ (F.shift n).map f :=
  (F.isoShift n).hom.naturality f

attribute [simp] isoShift_hom_naturality

@[reassoc]
/-
**CategoryTheory.Functor.isoShift_inv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：isoShift_inv_naturality (n : M) {X Y : C} (f : X ⟶ Y) : (F.shift n).map f 
≫ (F.isoShift n).inv.app Y = (F.isoShift n).inv.app X ≫ F.map (f⟦n⟧')
参数：n : M；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma isoShift_inv_naturality (n : M) {X Y : C} (f : X ⟶ Y) :
    (F.shift n).map f ≫ (F.isoShift n).inv.app Y =
      (F.isoShift n).inv.app X ≫ F.map (f⟦n⟧') :=
  (F.isoShift n).inv.naturality f
/-
**CategoryTheory.Functor.shiftIso_zero** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：shiftIso_zero (a : M) : F.shiftIso 0 a a (zero_add a) = isoWhiskerRight (s
hiftFunctorZero C M) _ ≪≫ leftUnitor _
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ShiftSequence.shiftIso_zero`：∀ {C : Type u_1} {A 
: Type u_3} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_3, u_3} A} {F : Categor…
-/
lemma shiftIso_zero (a : M) :
    F.shiftIso 0 a a (zero_add a) =
      isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _ :=
  ShiftSequence.shiftIso_zero a

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Functor.shiftIso_zero_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：shiftIso_zero_hom_app (a : M) (X : C) : (F.shiftIso 0 a a (zero_add a)).ho
m.app X = (shift F a).map ((shiftFunctorZero C M).hom.app X)
参数：a : M；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.shiftIso_zero`：shiftIso_zero (a : M) : F.shiftIso
 0 a a (zero_add a) = isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_zero_hom_app (a : M) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).hom.app X =
      (shift F a).map ((shiftFunctorZero C M).hom.app X) := by
  simp [F.shiftIso_zero a]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Functor.shiftIso_zero_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：shiftIso_zero_inv_app (a : M) (X : C) : (F.shiftIso 0 a a (zero_add a)).in
v.app X = (shift F a).map ((shiftFunctorZero C M).inv.app X)
参数：a : M；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.shiftIso_zero`：shiftIso_zero (a : M) : F.shiftIso
 0 a a (zero_add a) = isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_zero_inv_app (a : M) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).inv.app X =
      (shift F a).map ((shiftFunctorZero C M).inv.app X) := by
  simp [F.shiftIso_zero a]
/-
**CategoryTheory.Functor.shiftIso_add** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：shiftIso_add (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') :
 F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) = isoWhiskerRight (shif
tFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (F.shiftIso
 n a a' ha') ≪≫ F.shiftIso m a' a'' ha''
参数：n m a a' a'' : M；ha' : n + a = a'；ha'' : m + a' = a''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ShiftSequence.shiftIso_add`：∀ {C : Type u_1} {A :
 Type u_3} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryThe
ory.Category.{v_3, u_3} A} {F : Categor…
-/
lemma shiftIso_add (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (F.shiftIso n a a' ha') ≪≫ F.shiftIso m a' a'' ha'' :=
  ShiftSequence.shiftIso_add _ _ _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.shiftIso_add_hom_app** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：shiftIso_add_hom_app (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' 
= a'') (X : C) : (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).hom.a
pp X = (shift F a).map ((shiftFunctorAdd C m n).hom.app X) ≫ (shiftIso F n a a' 
ha').hom.app ((shiftFunctor C m).obj X) ≫ (shiftIso F m a' a'' ha'').hom.app X
参数：n m a a' a'' : M；ha' : n + a = a'；ha'' : m + a' = a''；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.shiftIso_add`：shiftIso_add (n m a a' a'' : M) (ha
' : n + a = a') (ha'' : m + a' = a'') : F.shiftIso (m + n) a a'' (by rw [add_ass
oc, ha', ha'']) = isoWhis…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_add_hom_app (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).hom.app X =
      (shift F a).map ((shiftFunctorAdd C m n).hom.app X) ≫
        (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
          (shiftIso F m a' a'' ha'').hom.app X := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.shiftIso_add_inv_app** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：shiftIso_add_inv_app (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' 
= a'') (X : C) : (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).inv.a
pp X = (shiftIso F m a' a'' ha'').inv.app X ≫ (shiftIso F n a a' ha').inv.app ((
shiftFunctor C m).obj X) ≫ (shift F a).map ((shiftFunctorAdd C m n).inv.app X)
参数：n m a a' a'' : M；ha' : n + a = a'；ha'' : m + a' = a''；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.shiftIso_add`：shiftIso_add (n m a a' a'' : M) (ha
' : n + a = a') (ha'' : m + a' = a'') : F.shiftIso (m + n) a a'' (by rw [add_ass
oc, ha', ha'']) = isoWhis…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_add_inv_app (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).inv.app X =
      (shiftIso F m a' a'' ha'').inv.app X ≫
        (shiftIso F n a a' ha').inv.app ((shiftFunctor C m).obj X) ≫
          (shift F a).map ((shiftFunctorAdd C m n).inv.app X) := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']
/-
**CategoryTheory.Functor.shiftIso_add'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：shiftIso_add' (n m mn : M) (hnm : m + n = mn) (a a' a'' : M) (ha' : n + a 
= a') (ha'' : m + a' = a'') : F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', 
add_assoc]) = isoWhiskerRight (shiftFunctorAdd' C m n _ hnm) _ ≪≫ Functor.associ
ator _ _ _ ≪≫ isoWhiskerLeft _ (F.shiftIso n a a' ha') ≪≫ F.shiftIso m a' a'' ha
''
参数：n m mn : M；hnm : m + n = mn；a a' a'' : M；ha' : n + a = a'；ha'' : m + a' = a''
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd`：∀ (C : Type u) {A : 
Type u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [in
st_2 : CategoryTheory.HasShift C A] (i j…
· 使用引理 `CategoryTheory.Functor.shiftIso_add`：shiftIso_add (n m a a' a'' : M) (ha
' : n + a = a') (ha'' : m + a' = a'') : F.shiftIso (m + n) a a'' (by rw [add_ass
oc, ha', ha'']) = isoWhis…
-/
lemma shiftIso_add' (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc]) =
      isoWhiskerRight (shiftFunctorAdd' C m n _ hnm) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (F.shiftIso n a a' ha') ≪≫ F.shiftIso m a' a'' ha'' := by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftIso_add]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.shiftIso_add'_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：∀ {C : Type u_1} {A : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} A] (F : CategoryTheory.Functo
r C A) {M : Type u_4} [inst_2 : AddMonoid M]   [inst_3 : CategoryTheory.HasShift
 C M] [inst_4 : F.ShiftSequence M] (n m mn : M) (hnm : m + n = mn) (a a' a'' : M
)   (ha' : n + a = a') (ha'' : m + a' = a'') (X : C),   (F.shiftIso mn a a'' ⋯).
hom.app X =     CategoryTheory.CategoryStruct.comp ((F.shift a).map ((CategoryTh
eory.shiftFunctorAdd' C m n mn hnm).hom.app X))       (CategoryTheory.CategorySt
ruct.comp ((F.shiftIso n a a' ha').hom.app ((CategoryTheory.shiftFunctor C m).ob
j X))         ((F.shiftIso m a' a'' ha'').hom.app X))
参数：F : CategoryTheory.Functor C A；n m mn : M；hnm : m + n = mn；a a' a'' : M；ha' :
 n + a = a'；ha'' : m + a' = a''；X : C；F.shiftIso mn a a'' ⋯；(F.shift a).map ((Ca
tegoryTheory.shiftFunctorAdd' C m n mn hnm).hom.app X)；CategoryTheory.CategorySt
ruct.comp ((F.shiftIso n a a' ha').hom.app ((CategoryTheory.shiftFunctor C m).ob
j X))         ((F.shiftIso m a' a'' ha'').hom.app X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.shiftIso_add'`：shiftIso_add' (n m mn : M) (hnm : 
m + n = mn) (a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') : F.shiftIso
 mn a a'' (by rw [← hnm, ←…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_add'_hom_app (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X =
      (shift F a).map ((shiftFunctorAdd' C m n mn hnm).hom.app X) ≫
        (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
          (shiftIso F m a' a'' ha'').hom.app X := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.shiftIso_add'_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：∀ {C : Type u_1} {A : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} A] (F : CategoryTheory.Functo
r C A) {M : Type u_4} [inst_2 : AddMonoid M]   [inst_3 : CategoryTheory.HasShift
 C M] [inst_4 : F.ShiftSequence M] (n m mn : M) (hnm : m + n = mn) (a a' a'' : M
)   (ha' : n + a = a') (ha'' : m + a' = a'') (X : C),   (F.shiftIso mn a a'' ⋯).
inv.app X =     CategoryTheory.CategoryStruct.comp ((F.shiftIso m a' a'' ha'').i
nv.app X)       (CategoryTheory.CategoryStruct.comp ((F.shiftIso n a a' ha').inv
.app ((CategoryTheory.shiftFunctor C m).obj X))         ((F.shift a).map ((Categ
oryTheory.shiftFunctorAdd' C m n mn hnm).inv.app X)))
参数：F : CategoryTheory.Functor C A；n m mn : M；hnm : m + n = mn；a a' a'' : M；ha' :
 n + a = a'；ha'' : m + a' = a''；X : C；F.shiftIso mn a a'' ⋯；(F.shiftIso m a' a''
 ha'').inv.app X；CategoryTheory.CategoryStruct.comp ((F.shiftIso n a a' ha').inv
.app ((CategoryTheory.shiftFunctor C m).obj X))         ((F.shift a).map ((Categ
oryTheory.shiftFunctorAdd' C m n mn hnm).inv.app X))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.shiftIso_add'`：shiftIso_add' (n m mn : M) (hnm : 
m + n = mn) (a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') : F.shiftIso
 mn a a'' (by rw [← hnm, ←…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftIso_add'_inv_app (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).inv.app X =
      (shiftIso F m a' a'' ha'').inv.app X ≫
        (shiftIso F n a a' ha').inv.app ((shiftFunctor C m).obj X) ≫
        (shift F a).map ((shiftFunctorAdd' C m n mn hnm).inv.app X) := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

@[reassoc]
/-
**CategoryTheory.Functor.shiftIso_hom_app_comp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：shiftIso_hom_app_comp (n m mn : M) (hnm : m + n = mn) (a a' a'' : M) (ha' 
: n + a = a') (ha'' : m + a' = a'') (X : C) : (shiftIso F n a a' ha').hom.app ((
shiftFunctor C m).obj X) ≫ (shiftIso F m a' a'' ha'').hom.app X = (shift F a).ma
p ((shiftFunctorAdd' C m n mn hnm).inv.app X) ≫ (F.shiftIso mn a a'' (by rw [← h
nm, ← ha'', ← ha', add_assoc])).hom.app X
参数：n m mn : M；hnm : m + n = mn；a a' a'' : M；ha' : n + a = a'；ha'' : m + a' = a''
；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.shiftIso_add'_hom_app`：∀ {C : Type u_1} {A : Type
 u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_3, u_3} A] (F : Categor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma shiftIso_hom_app_comp (n m mn : M) (hnm : m + n = mn)
    (a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
      (shiftIso F m a' a'' ha'').hom.app X =
        (shift F a).map ((shiftFunctorAdd' C m n mn hnm).inv.app X) ≫
          (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X := by
  rw [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'', ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id, id_comp]

/-- The morphism `(F.shift a).obj X ⟶ (F.shift a').obj Y` induced by a morphism
`f : X ⟶ Y⟦n⟧` when `n + a = a'`. -/
/-
**CategoryTheory.Functor.shiftMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：shiftMap {X Y : C} {n : M} (f : X ⟶ Y⟦n⟧) (a a' : M) (ha' : n + a = a') : 
(F.shift a).obj X ⟶ (F.shift a').obj Y
参数：f : X ⟶ Y⟦n⟧；a a' : M；ha' : n + a = a'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `(F.shift a).obj X ⟶ (F.shift a').obj Y` induced by a morphism
`f : X ⟶ Y⟦n⟧` when `n + a = a'`.
-/
def shiftMap {X Y : C} {n : M} (f : X ⟶ Y⟦n⟧) (a a' : M) (ha' : n + a = a') :
    (F.shift a).obj X ⟶ (F.shift a').obj Y :=
  (F.shift a).map f ≫ (F.shiftIso _ _ _ ha').hom.app Y

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Functor.shiftMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：shiftMap_comp {X Y Z : C} {n : M} (f : X ⟶ Y⟦n⟧) (g : Y ⟶ Z) (a a' : M) (h
a' : n + a = a') : F.shiftMap (f ≫ g⟦n⟧') a a' ha' = F.shiftMap f a a' ha' ≫ (F.
shift a').map g
参数：f : X ⟶ Y⟦n⟧；g : Y ⟶ Z；a a' : M；ha' : n + a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Functor.shiftIso_hom_naturality`：shiftIso_hom_naturality 
{X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y) : (shift F a).map (f⟦n⟧') 
≫ (shiftIso F n a a' ha').hom.app Y …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftMap_comp {X Y Z : C} {n : M} (f : X ⟶ Y⟦n⟧) (g : Y ⟶ Z) (a a' : M) (ha' : n + a = a') :
    F.shiftMap (f ≫ g⟦n⟧') a a' ha' = F.shiftMap f a a' ha' ≫ (F.shift a').map g := by
  simp [shiftMap]

@[reassoc]
/-
**CategoryTheory.Functor.shiftMap_comp'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：shiftMap_comp' {X Y Z : C} {n : M} (f : X ⟶ Y) (g : Y ⟶ Z⟦n⟧) (a a' : M) (
ha' : n + a = a') : F.shiftMap (f ≫ g) a a' ha' = (F.shift a).map f ≫ F.shiftMap
 g a a' ha'
参数：f : X ⟶ Y；g : Y ⟶ Z⟦n⟧；a a' : M；ha' : n + a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftMap_comp' {X Y Z : C} {n : M} (f : X ⟶ Y) (g : Y ⟶ Z⟦n⟧) (a a' : M) (ha' : n + a = a') :
    F.shiftMap (f ≫ g) a a' ha' = (F.shift a).map f ≫ F.shiftMap g a a' ha' := by
  simp [shiftMap]

/--
When `f : X ⟶ Y⟦m⟧`, `m + n = mn`, `n + a = a'` and `ha'' : m + a' = a''`, this lemma
relates the two morphisms `F.shiftMap f a' a'' ha''` and `(F.shift a).map (f⟦n⟧')`. Indeed,
via canonical isomorphisms, they both identify to morphisms
`(F.shift a').obj X ⟶ (F.shift a'').obj Y`.
-/
/-
**CategoryTheory.Functor.shiftIso_hom_app_comp_shiftMap** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：shiftIso_hom_app_comp_shiftMap {X Y : C} {m : M} (f : X ⟶ Y⟦m⟧) (n mn : M)
 (hnm : m + n = mn) (a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') : (F
.shiftIso n a a' ha').hom.app X ≫ F.shiftMap f a' a'' ha'' = (F.shift a).map (f⟦
n⟧') ≫ (F.shift a).map ((shiftFunctorAdd' C m n mn hnm).inv.app Y) ≫ (F.shiftIso
 mn a a'' (by rw [← ha'', ← ha', ← hnm, add_assoc])).hom.app Y
参数：f : X ⟶ Y⟦m⟧；n mn : M；hnm : m + n = mn；a a' a'' : M；ha' : n + a = a'；ha'' : m
 + a' = a''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.shiftIso_add'_hom_app`：∀ {C : Type u_1} {A : Type
 u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.C
ategory.{v_3, u_3} A] (F : Categor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.shiftIso_hom_naturality_assoc`：∀ {C : Type u_1} {
A : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Category
Theory.Category.{v_3, u_3} A] (F : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When `f : X ⟶ Y⟦m⟧`, `m + n = mn`, `n + a = a'` and `ha'' : m + a' = a''`, this 
lemma
relates the two morphisms `F.shiftMap f a' a'' ha''` and `(F.shift a).map (f⟦n⟧'
)`. Indeed,
via canonical isomorphisms, they both identify to morphisms
`(F.shift a').obj X ⟶ (F.shift a'').obj Y`.
-/
lemma shiftIso_hom_app_comp_shiftMap {X Y : C} {m : M} (f : X ⟶ Y⟦m⟧) (n mn : M) (hnm : m + n = mn)
    (a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') :
    (F.shiftIso n a a' ha').hom.app X ≫ F.shiftMap f a' a'' ha'' =
      (F.shift a).map (f⟦n⟧') ≫ (F.shift a).map ((shiftFunctorAdd' C m n mn hnm).inv.app Y) ≫
        (F.shiftIso mn a a'' (by rw [← ha'', ← ha', ← hnm, add_assoc])).hom.app Y := by
  simp only [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'' Y,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    id_comp, comp_obj, shiftIso_hom_naturality_assoc, shiftMap]

/--
If `f : X ⟶ Y⟦m⟧`, `n + m = 0` and `ha' : m + a = a'`, this lemma relates the two
morphisms `F.shiftMap f a a' ha'` and `(F.shift a').map (f⟦n⟧')`. Indeed,
via canonical isomorphisms, they both identify to morphisms
`(F.shift a).obj X ⟶ (F.shift a').obj Y`.
-/
/-
**CategoryTheory.Functor.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：shiftIso_hom_app_comp_shiftMap_of_add_eq_zero [F.ShiftSequence G] {X Y : C
} {m : G} (f : X ⟶ Y⟦m⟧) (n : G) (hnm : n + m = 0) (a a' : G) (ha' : m + a = a')
 : (F.shiftIso n a' a (by rw [← ha', ← add_assoc, hnm, zero_add])).hom.app X ≫ F
.shiftMap f a a' ha' = (F.shift a').map (f⟦n⟧' ≫ (shiftFunctorCompIsoId C m n (b
y rw [← add_left_inj m, add_assoc, hnm, zero_add, add_zero])).hom.app Y)
参数：f : X ⟶ Y⟦m⟧；n : G；hnm : n + m = 0；a a' : G；ha' : m + a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Functor.shiftIso_hom_app_comp_shiftMap`：shiftIso_hom_app_
comp_shiftMap {X Y : C} {m : M} (f : X ⟶ Y⟦m⟧) (n mn : M) (hnm : m + n = mn) (a 
a' a'' : M) (ha' : n + a = a') (ha'' : m + …
· 使用引理 `CategoryTheory.Functor.shiftIso_zero_hom_app`：shiftIso_zero_hom_app (a :
 M) (X : C) : (F.shiftIso 0 a a (zero_add a)).hom.app X = (shift F a).map ((shif
tFunctorZero C M).hom.app X)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f : X ⟶ Y⟦m⟧`, `n + m = 0` and `ha' : m + a = a'`, this lemma relates the tw
o
morphisms `F.shiftMap f a a' ha'` and `(F.shift a').map (f⟦n⟧')`. Indeed,
via canonical isomorphisms, they both identify to morphisms
`(F.shift a).obj X ⟶ (F.shift a').obj Y`.
-/
lemma shiftIso_hom_app_comp_shiftMap_of_add_eq_zero [F.ShiftSequence G]
    {X Y : C} {m : G} (f : X ⟶ Y⟦m⟧)
    (n : G) (hnm : n + m = 0) (a a' : G) (ha' : m + a = a') :
    (F.shiftIso n a' a (by rw [← ha', ← add_assoc, hnm, zero_add])).hom.app X ≫
      F.shiftMap f a a' ha' =
    (F.shift a').map (f⟦n⟧' ≫ (shiftFunctorCompIsoId C m n
      (by rw [← add_left_inj m, add_assoc, hnm, zero_add, add_zero])).hom.app Y) := by
  have hnm' : m + n = 0 := by
    rw [← add_left_inj m, add_assoc, hnm, zero_add, add_zero]
  simp [F.shiftIso_hom_app_comp_shiftMap f n 0 hnm' a' a, shiftIso_zero_hom_app,
    shiftFunctorCompIsoId]

section

variable [HasZeroMorphisms C] [HasZeroMorphisms A] [F.PreservesZeroMorphisms]
  [∀ (n : M), (shiftFunctor C n).PreservesZeroMorphisms]

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : M) : (F.shift n).PreservesZeroMorphisms :=
  preservesZeroMorphisms_of_iso (F.isoShift n)

@[simp]
/-
**CategoryTheory.Functor.shiftMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：shiftMap_zero (X Y : C) (n a a' : M) (ha' : n + a = a') : F.shiftMap (0 : 
X ⟶ Y⟦n⟧) a a' ha' = 0
参数：X Y : C；n a a' : M；ha' : n + a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.instPreservesZeroMorphismsShift`：∀ {C : Type u_1}
 {A : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_3, u_3} A] (F : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shiftMap_zero (X Y : C) (n a a' : M) (ha' : n + a = a') :
    F.shiftMap (0 : X ⟶ Y⟦n⟧) a a' ha' = 0 := by
  simp [shiftMap]

end

section

variable [Preadditive C] [Preadditive A] [F.Additive]
  [∀ (n : M), (shiftFunctor C n).Additive]

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : M) : (F.shift n).Additive := additive_of_iso (F.isoShift n)

end

end

namespace ShiftSequence

variable {F} in
set_option backward.isDefEq.respectTransparency false in
/-- Given an isomorphism `π ⋙ H ≅ F`, where `π` is a functor which commutes
with the shift by `M` and `H` is equipped with a shift sequence,
then this is the shift sequence for `F` induced by composition. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.ShiftSequence.leftComp** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor.ShiftSequence`。
形式化陈述：leftComp [π.CommShift M] [H.ShiftSequence M] : F.ShiftSequence M where seq
uence n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an isomorphism `π ⋙ H ≅ F`, where `π` is a functor which commutes
with the shift by `M` and `H` is equipped with a shift sequence,
then this is the shift sequence for `F` induced by composition.
-/
def leftComp [π.CommShift M] [H.ShiftSequence M] : F.ShiftSequence M where
  sequence n := π ⋙ H.shift n
  isoZero := isoWhiskerLeft π (H.isoShiftZero M) ≪≫ e
  shiftIso n a a' ha' :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (π.commShiftIso n) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft π (H.shiftIso n a a' ha')
  shiftIso_zero a := by
    ext K
    simp [← Functor.map_comp, commShiftIso_zero]
  shiftIso_add n m a a' a'' ha' ha'':= by
    ext K
    dsimp
    simp only [H.shiftIso_add_hom_app n m a a' a'' ha' ha'', assoc,
      commShiftIso_add, CommShift.isoAdd_hom_app, ← Functor.map_comp_assoc,
      id_comp, Iso.inv_hom_id_app, comp_obj, comp_id]
    simp
/-
**CategoryTheory.Functor.ShiftSequence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Functor.ShiftSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [π.CommShift M] [H.ShiftSequence M] : (π ⋙ H).ShiftSequence M :=
  leftComp (Iso.refl _) _

end ShiftSequence

end Functor

end CategoryTheory

