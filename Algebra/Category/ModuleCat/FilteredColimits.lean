/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# The forgetful functor from `R`-modules preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a ring `R`, a small filtered category `J` and a functor
`F : J ⥤ ModuleCat R`. We show that the colimit of `F ⋙ forget₂ (ModuleCat R) AddCommGrpCat`
(in `AddCommGrpCat`) carries the structure of an `R`-module, thereby showing that the forgetful
functor `forget₂ (ModuleCat R) AddCommGrpCat` preserves filtered colimits. In particular, this
implies that `forget (ModuleCat R)` preserves filtered colimits.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory Limits ConcreteCategory

open CategoryTheory.IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

namespace ModuleCat.FilteredColimits

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ ModuleCat.{max v u, u} R)

/-- The colimit of `F ⋙ forget₂ (ModuleCat R) AddCommGrpCat` in the category `AddCommGrpCat`.
In the following, we will show that this has the structure of an `R`-module.
-/
/-
**ModuleCat.FilteredColimits.M** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.FilteredColi
mits`。
形式化陈述：M : AddCommGrpCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of `F ⋙ forget₂ (ModuleCat R) AddCommGrpCat` in the category `AddCom
mGrpCat`.
In the following, we will show that this has the structure of an `R`-module.
-/
def M : AddCommGrpCat :=
  AddCommGrpCat.FilteredColimits.colimit.{v, u}
    (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{max v u})

/-- The canonical projection into the colimit, as a quotient type. -/
/-
**ModuleCat.FilteredColimits.M.mk** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.FilteredC
olimits.M`。
形式化陈述：{R : Type u} →   [inst : Ring R] →     {J : Type v} →       [inst_1 : Cate
goryTheory.SmallCategory J] →         [inst_2 : CategoryTheory.IsFiltered J] →  
         (F : CategoryTheory.Functor J (ModuleCat R)) → (j : J) × ↑(F.obj j) → ↑
(ModuleCat.FilteredColimits.M F)
参数：F : CategoryTheory.Functor J (ModuleCat R)；j : J；F.obj j；ModuleCat.FilteredCo
limits.M F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection into the colimit, as a quotient type.
-/
def M.mk : (Σ j, F.obj j) → M F :=
  fun x ↦ (F ⋙ forget (ModuleCat R)).ιColimitType x.1 x.2
/-
**ModuleCat.FilteredColimits.M.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCa
t.FilteredColimits.M`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {J : Type v} [inst_1 : CategoryTheory.Small
Category J]   [inst_2 : CategoryTheory.IsFiltered J] (F : CategoryTheory.Functor
 J (ModuleCat R))   (m : ↑(ModuleCat.FilteredColimits.M F)), ∃ j x, ModuleCat.Fi
lteredColimits.M.mk F ⟨j, x⟩ = m
参数：F : CategoryTheory.Functor J (ModuleCat R)；m : ↑(ModuleCat.FilteredColimits.M
 F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.ιColimitType_jointly_surjective`：ιColimitType_joi
ntly_surjective (t : F.ColimitType) : exists j x, F.ιColimitType j x = t
-/
lemma M.mk_surjective (m : M F) :
    ∃ (j : J) (x : F.obj j), M.mk F ⟨j, x⟩ = m :=
  (F ⋙ forget (ModuleCat R)).ιColimitType_jointly_surjective m
/-
**ModuleCat.FilteredColimits.M.mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.Filter
edColimits.M`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {J : Type v} [inst_1 : CategoryTheory.Small
Category J]   [inst_2 : CategoryTheory.IsFiltered J] (F : CategoryTheory.Functor
 J (ModuleCat R)) (x y : (j : J) × ↑(F.obj j)),   (∃ k f g,       (CategoryTheor
y.ConcreteCategory.hom (F.map f)) x.snd = (CategoryTheory.ConcreteCategory.hom (
F.map g)) y.snd) →     ModuleCat.FilteredColimits.M.mk F x = ModuleCat.FilteredC
olimits.M.mk F y
参数：F : CategoryTheory.Functor J (ModuleCat R)；x y : (j : J) × ↑(F.obj j)；∃ k f g
,       (CategoryTheory.ConcreteCategory.hom (F.map f)) x.snd = (CategoryTheory.
ConcreteCategory.hom (F.map g)) y.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.eqvGen_sound`：Quot.eqvGen_sound (H : EqvGen r a b) : Quot.mk r a = 
Quot.mk r b
· 使用定理 `CategoryTheory.Limits.Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel
`：eqvGen_colimitTypeRel_of_rel (x y : Σ j, F.obj j) : FilteredColimit.Rel.{v, u}
 F x y -> Relation.EqvGen F.ColimitTypeRel x y
-/
theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : M.mk F x = M.mk F y :=
  Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel
    (F ⋙ forget (ModuleCat R)) x y h)
/-
**ModuleCat.FilteredColimits.M.mk_map** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat.Filte
redColimits.M`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {J : Type v} [inst_1 : CategoryTheory.Small
Category J]   [inst_2 : CategoryTheory.IsFiltered J] (F : CategoryTheory.Functor
 J (ModuleCat R)) {j k : J} (f : j ⟶ k)   (x : ↑(F.obj j)),   ModuleCat.Filtered
Colimits.M.mk F ⟨k, (CategoryTheory.ConcreteCategory.hom (F.map f)) x⟩ =     Mod
uleCat.FilteredColimits.M.mk F ⟨j, x⟩
参数：F : CategoryTheory.Functor J (ModuleCat R)；f : j ⟶ k；x : ↑(F.obj j)；CategoryT
heory.ConcreteCategory.hom (F.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.FilteredColimits.M.mk_eq`：∀ {R : Type u} [inst : Ring R] {J : 
Type v} [inst_1 : CategoryTheory.SmallCategory J]   [inst_2 : CategoryTheory.IsF
iltered J] (F : Category…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma M.mk_map {j k : J} (f : j ⟶ k) (x : F.obj j) :
    M.mk F ⟨k, F.map f x⟩ = M.mk F ⟨j, x⟩ :=
  M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

/-- The "unlifted" version of scalar multiplication in the colimit. -/
/-
**ModuleCat.FilteredColimits.colimitSMulAux** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat
.FilteredColimits`。
形式化陈述：colimitSMulAux (r : R) (x : Σ j, F.obj j) : M F
参数：r : R；x : Σ j, F.obj j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "unlifted" version of scalar multiplication in the colimit.
-/
def colimitSMulAux (r : R) (x : Σ j, F.obj j) : M F :=
  M.mk F ⟨x.1, r • x.2⟩

set_option backward.defeqAttrib.useBackward true in
/-
**ModuleCat.FilteredColimits.colimitSMulAux_eq_of_rel** 是 Mathlib 中的一个定理，位于命名空间 
`ModuleCat.FilteredColimits`。
形式化陈述：colimitSMulAux_eq_of_rel (r : R) (x y : Σ j, F.obj j) (h : Types.FilteredC
olimit.Rel (F ⋙ forget (ModuleCat R)) x y) : colimitSMulAux F r x = colimitSMulA
ux F r y
参数：r : R；x y : Σ j, F.obj j；h : Types.FilteredColimit.Rel (F ⋙ forget (ModuleCat
 R)) x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.FilteredColimits.M.mk_eq`：∀ {R : Type u} [inst : Ring R] {J : 
Type v} [inst_1 : CategoryTheory.SmallCategory J]   [inst_2 : CategoryTheory.IsF
iltered J] (F : Category…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem colimitSMulAux_eq_of_rel (r : R) (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget (ModuleCat R)) x y) :
    colimitSMulAux F r x = colimitSMulAux F r y := by
  apply M.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk] at hfg
  simp [hfg]

/-- Scalar multiplication in the colimit. See also `colimitSMulAux`. -/
/-
**ModuleCat.FilteredColimits.colimitHasSMul** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat
.FilteredColimits`。
形式化陈述：colimitHasSMul : SMul R (M F) where smul r x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication in the colimit. See also `colimitSMulAux`.
-/
instance colimitHasSMul : SMul R (M F) where
  smul r x := by
    refine Quot.lift (colimitSMulAux F r) ?_ x
    intro x y h
    apply colimitSMulAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_colimitTypeRel
    exact h
/-
**ModuleCat.FilteredColimits.colimit_zero_eq** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCa
t.FilteredColimits`。
形式化陈述：colimit_zero_eq (j : J) : 0 = M.mk F ⟨j, 0⟩
参数：j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonCat.FilteredColimits.colimit_zero_eq`：∀ {J : Type v} [inst : Categ
oryTheory.SmallCategory J] (F : CategoryTheory.Functor J AddMonCat)   [inst_1 : 
CategoryTheory.IsFiltered J] (j …
-/
lemma colimit_zero_eq (j : J) :
    0 = M.mk F ⟨j, 0⟩ := by
  apply AddMonCat.FilteredColimits.colimit_zero_eq
/-
**ModuleCat.FilteredColimits.colimit_add_mk_eq** 是 Mathlib 中的一个引理，位于命名空间 `Module
Cat.FilteredColimits`。
形式化陈述：colimit_add_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k)
 : M.mk _ x + M.mk _ y = M.mk _ ⟨k, F.map f x.2 + F.map g y.2⟩
参数：x y : Σ j, F.obj j；k : J；f : x.1 ⟶ k；g : y.1 ⟶ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonCat.FilteredColimits.colimit_add_mk_eq`：∀ {J : Type v} [inst : Cat
egoryTheory.SmallCategory J] (F : CategoryTheory.Functor J AddMonCat)   [inst_1 
: CategoryTheory.IsFiltered J] (x …
-/
lemma colimit_add_mk_eq (x y : Σ j, F.obj j) (k : J)
    (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk _ x + M.mk _ y = M.mk _ ⟨k, F.map f x.2 + F.map g y.2⟩ := by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq
/-
**ModuleCat.FilteredColimits.colimit_add_mk_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Modul
eCat.FilteredColimits`。
形式化陈述：colimit_add_mk_eq' {j : J} (x y : F.obj j) : M.mk F ⟨j, x⟩ + M.mk F ⟨j, y⟩
 = M.mk F ⟨j, x + y⟩
参数：x y : F.obj j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonCat.FilteredColimits.colimit_add_mk_eq'`：∀ {J : Type v} [inst : Ca
tegoryTheory.SmallCategory J] (F : CategoryTheory.Functor J AddMonCat)   [inst_1
 : CategoryTheory.IsFiltered J] {j …
-/
lemma colimit_add_mk_eq' {j : J} (x y : F.obj j) :
    M.mk F ⟨j, x⟩ + M.mk F ⟨j, y⟩ = M.mk F ⟨j, x + y⟩ := by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq'

@[simp]
/-
**ModuleCat.FilteredColimits.colimit_smul_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Modul
eCat.FilteredColimits`。
形式化陈述：colimit_smul_mk_eq (r : R) (x : Σ j, F.obj j) : r • M.mk F x = M.mk F ⟨x.1
, r • x.2⟩
参数：r : R；x : Σ j, F.obj j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit_smul_mk_eq (r : R) (x : Σ j, F.obj j) : r • M.mk F x = M.mk F ⟨x.1, r • x.2⟩ :=
  rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11083): writing directly the `Module` instance makes things very slow.
/-
**ModuleCat.FilteredColimits.colimitMulAction** 是 Mathlib 中的一个实例，位于命名空间 `ModuleC
at.FilteredColimits`。
形式化陈述：colimitMulAction : MulAction R (M F) where one_smul x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance colimitMulAction : MulAction R (M F) where
  one_smul x := by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp
  mul_smul r s x := by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp [mul_smul]
/-
**ModuleCat.FilteredColimits.colimitSMulWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Modu
leCat.FilteredColimits`。
形式化陈述：colimitSMulWithZero : SMulWithZero R (M F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance colimitSMulWithZero : SMulWithZero R (M F) :=
{ colimitMulAction F with
  smul_zero := fun r => by
    rw [colimit_zero_eq _ (IsFiltered.nonempty.some : J), colimit_smul_mk_eq, smul_zero]
  zero_smul := fun x => by
    obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
    simp [← colimit_zero_eq] }
/-
**ModuleCat.FilteredColimits.colimitModule** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.
FilteredColimits`。
形式化陈述：colimitModule : Module R (M F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance colimitModule : Module R (M F) :=
{ colimitMulAction F,
  colimitSMulWithZero F with
  smul_add := fun r x y => by
    obtain ⟨i, x, rfl⟩ := M.mk_surjective F x
    obtain ⟨j, y, rfl⟩ := M.mk_surjective F y
    rw [colimit_smul_mk_eq, colimit_smul_mk_eq,
      colimit_add_mk_eq _ ⟨i, _⟩ ⟨j, _⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j), colimit_smul_mk_eq, smul_add,
      colimit_add_mk_eq _ ⟨i, _⟩ ⟨j, _⟩ (max' i j) (IsFiltered.leftToMax i j)
      (IsFiltered.rightToMax i j), map_smul, map_smul]
  add_smul r s x := by
    obtain ⟨i, x, rfl⟩ := M.mk_surjective F x
    simp [_root_.add_smul, colimit_add_mk_eq'] }

/-- The bundled `R`-module giving the filtered colimit of a diagram. -/
/-
**ModuleCat.FilteredColimits.colimit** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Filter
edColimits`。
形式化陈述：colimit : ModuleCat.{max v u, u} R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bundled `R`-module giving the filtered colimit of a diagram.
-/
def colimit : ModuleCat.{max v u, u} R :=
  ModuleCat.of R (M F)

/-- The linear map from a given `R`-module in the diagram to the colimit module. -/
/-
**ModuleCat.FilteredColimits.coconeMorphism** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat
.FilteredColimits`。
形式化陈述：coconeMorphism (j : J) : F.obj j ⟶ colimit F
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from a given `R`-module in the diagram to the colimit module.
-/
def coconeMorphism (j : J) : F.obj j ⟶ colimit F :=
  ofHom
    { ((AddCommGrpCat.FilteredColimits.colimitCocone
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{max v u})).ι.app j).hom with
    map_smul' := by solve_by_elim }

/-- The cocone over the proposed colimit module. -/
@[implicit_reducible]
/-
**ModuleCat.FilteredColimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.
FilteredColimits`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone over the proposed colimit module.
-/
def colimitCocone : Cocone F where
  pt := colimit F
  ι :=
    { app := coconeMorphism F
      naturality _ _ f := by
        ext
        simpa using! (Types.TypeMax.colimitCocone
          (F ⋙ forget (ModuleCat R))).ι.naturality_apply f _ }

set_option backward.isDefEq.respectTransparency false in
/-- Given a cocone `t` of `F`, the induced monoid linear map from the colimit to the cocone point.
We already know that this is a morphism between additive groups. The only thing left to see is that
it is a linear map, i.e. preserves scalar multiplication.
-/
/-
**ModuleCat.FilteredColimits.colimitDesc** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Fi
lteredColimits`。
形式化陈述：colimitDesc (t : Cocone F) : colimit F ⟶ t.pt
参数：t : Cocone F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cocone `t` of `F`, the induced monoid linear map from the colimit to the
 cocone point.
We already know that this is a morphism between additive groups. The only thing 
left to see is that
it is a linear map, i.e. preserves scalar multiplication.
-/
def colimitDesc (t : Cocone F) : colimit F ⟶ t.pt :=
  let h := (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _))
  let f : colimit F →+ t.pt := (h.desc ((forget₂ _ _).mapCocone t)).hom
  have hf {j : J} (x : F.obj j) : f (M.mk _ ⟨j, x⟩) = t.ι.app j x :=
    congr_hom ((forget AddCommGrpCat).congr_map (h.fac ((forget₂ _ _).mapCocone t) j)) x
  ofHom
    { f with
      map_smul' := fun r x => by
        obtain ⟨j, x, rfl⟩ := M.mk_surjective F x
        simp [hf] }

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**ModuleCat.FilteredColimits.** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.FilteredColim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_colimitDesc (t : Cocone F) (j : J) :
    dsimp% (colimitCocone F).ι.app j ≫ colimitDesc F t = t.ι.app j :=
  (forget₂ _ AddCommGrpCat).map_injective
    ((AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _)).fac _ _)

/-- The proposed colimit cocone is a colimit in `ModuleCat R`. -/
/-
**ModuleCat.FilteredColimits.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `M
oduleCat.FilteredColimits`。
形式化陈述：colimitCoconeIsColimit : IsColimit (colimitCocone F) where desc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposed colimit cocone is a colimit in `ModuleCat R`.
-/
def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc := colimitDesc F
  fac t j := by simp
  uniq t _ h := by
    ext ⟨j, x⟩
    exact (congr_hom ((forget (ModuleCat _)).congr_map (h j)) _).trans
      (congr_hom ((forget (ModuleCat _)).congr_map (ι_colimitDesc F t j)) x).symm
/-
**ModuleCat.FilteredColimits.forget** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat.Filtere
dColimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂AddCommGroup_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
  { preservesColimit := fun {F} =>
      preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F)
        (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) }
/-
**ModuleCat.FilteredColimits.forget_preservesFilteredColimits** 是 Mathlib 中的一个实例
，位于命名空间 `ModuleCat.FilteredColimits`。
形式化陈述：forget_preservesFilteredColimits : PreservesFilteredColimits (forget (Modu
leCat.{u} R))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`：Categor
yTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat)
-/
instance forget_preservesFilteredColimits : PreservesFilteredColimits (forget (ModuleCat.{u} R)) :=
  Limits.comp_preservesFilteredColimits (forget₂ (ModuleCat R) AddCommGrpCat)
    (forget AddCommGrpCat)
/-
**ModuleCat.FilteredColimits.forget_reflectsFilteredColimits** 是 Mathlib 中的一个实例，
位于命名空间 `ModuleCat.FilteredColimits`。
形式化陈述：forget_reflectsFilteredColimits : ReflectsFilteredColimits (forget (Module
Cat.{u} R)) where reflects_filtered_colimits _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimit_of_reflectsIsomorphisms`：reflectsC
olimit_of_reflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [G.ReflectsIsomorphisms] 
[HasColimit F] [PreservesColimit F G] : ReflectsCol…
· 使用定理 `ModuleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier`：∀ {R : Type 
u} [inst : Ring R], (CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms
· 使用定理 `ModuleCat.HasColimit.instHasColimit`：∀ {R : Type w} [inst : Ring R] {J :
 Type u} [inst_1 : CategoryTheory.Category.{v, u} J]   (F : CategoryTheory.Funct
or J (ModuleCat R))   [Ca…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance forget_reflectsFilteredColimits : ReflectsFilteredColimits (forget (ModuleCat.{u} R)) where
  reflects_filtered_colimits _ := { reflectsColimit := reflectsColimit_of_reflectsIsomorphisms _ _ }

end

end ModuleCat.FilteredColimits

