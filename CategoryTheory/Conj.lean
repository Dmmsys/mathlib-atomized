/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.HomCongr

/-!
# Conjugate morphisms by isomorphisms

An isomorphism `α : X ≅ Y` defines
- a monoid isomorphism
  `CategoryTheory.Iso.conj : End X ≃* End Y` by `α.conj f = α.inv ≫ f ≫ α.hom`;
- a group isomorphism `CategoryTheory.Iso.conjAut : Aut X ≃* Aut Y` by
  `α.conjAut f = α.symm ≪≫ f ≪≫ α`
  using
  `CategoryTheory.Iso.homCongr : (X ≅ X₁) → (Y ≅ Y₁) → (X ⟶ Y) ≃ (X₁ ⟶ Y₁)`
  and `CategoryTheory.Iso.isoCongr : (f : X₁ ≅ X₂) → (g : Y₁ ≅ Y₂) → (X₁ ≅ Y₁) ≃ (X₂ ≅ Y₂)`
  which are defined in  `CategoryTheory.HomCongr`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace Iso

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (α : X ≅ Y)

/-- An isomorphism between two objects defines a monoid isomorphism between their
monoid of endomorphisms. -/
/-
**CategoryTheory.Iso.conj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：conj : End X ≃* End Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.homCongr_comp`：homCongr_comp {X Y Z X₁ Y₁ Z₁ : C} (α 
: X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁) (f : X ⟶ Y) (g : Y ⟶ Z) : α.homCongr γ (f ≫ 
g) = α.homCongr β f ≫ …

--- 原说明 ---
An isomorphism between two objects defines a monoid isomorphism between their
monoid of endomorphisms.
-/
def conj : End X ≃* End Y :=
  { homCongr α α with map_mul' := fun f g => homCongr_comp α α α g f }
/-
**CategoryTheory.Iso.conj_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：conj_apply (f : End X) : α.conj f = α.inv ≫ f ≫ α.hom
参数：f : End X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_apply (f : End X) : α.conj f = α.inv ≫ f ≫ α.hom :=
  rfl

@[simp]
/-
**CategoryTheory.Iso.conj_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：conj_comp (f g : End X) : α.conj (f ≫ g) = α.conj f ≫ α.conj g
参数：f g : End X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem conj_comp (f g : End X) : α.conj (f ≫ g) = α.conj f ≫ α.conj g :=
  map_mul α.conj g f

@[simp]
/-
**CategoryTheory.Iso.conj_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：conj_id : α.conj (𝟙 X) = 𝟙 Y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem conj_id : α.conj (𝟙 X) = 𝟙 Y :=
  map_one α.conj

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Iso.refl_conj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：refl_conj (f : End X) : (Iso.refl X).conj f = f
参数：f : End X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.conj_apply`：conj_apply (f : End X) : α.conj f = α.inv
 ≫ f ≫ α.hom
· 使用定理 `CategoryTheory.Iso.refl_inv`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] (X : C),   (CategoryTheory.Iso.refl X).inv = CategoryTheory.Catego
ryStruct.id X
· 使用定理 `CategoryTheory.Iso.refl_hom`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] (X : C),   (CategoryTheory.Iso.refl X).hom = CategoryTheory.Catego
ryStruct.id X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem refl_conj (f : End X) : (Iso.refl X).conj f = f := by
  rw [conj_apply, Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

@[simp]
/-
**CategoryTheory.Iso.trans_conj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：trans_conj {Z : C} (β : Y ≅ Z) (f : End X) : (α ≪≫ β).conj f = β.conj (α.c
onj f)
参数：β : Y ≅ Z；f : End X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.homCongr_trans`：homCongr_trans {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C
} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂) (α₂ : X₂ ≅ X₃) (β₂ : Y₂ ≅ Y₃) (f : X₁ ⟶ Y₁) : (α
₁ ≪≫ α₂).homCongr (β₁ ≪…
-/
theorem trans_conj {Z : C} (β : Y ≅ Z) (f : End X) : (α ≪≫ β).conj f = β.conj (α.conj f) :=
  homCongr_trans α α β β f

@[simp]
/-
**CategoryTheory.Iso.symm_self_conj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：symm_self_conj (f : End X) : α.symm.conj (α.conj f) = f
参数：f : End X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.trans_conj`：trans_conj {Z : C} (β : Y ≅ Z) (f : End X
) : (α ≪≫ β).conj f = β.conj (α.conj f)
· 使用定理 `CategoryTheory.Iso.self_symm_id`：self_symm_id (α : X ≅ Y) : α ≪≫ α.symm 
= Iso.refl X
· 使用定理 `CategoryTheory.Iso.refl_conj`：refl_conj (f : End X) : (Iso.refl X).conj 
f = f
-/
theorem symm_self_conj (f : End X) : α.symm.conj (α.conj f) = f := by
  rw [← trans_conj, α.self_symm_id, refl_conj]

@[simp]
/-
**CategoryTheory.Iso.self_symm_conj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：self_symm_conj (f : End Y) : α.conj (α.symm.conj f) = f
参数：f : End Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.symm_self_conj`：symm_self_conj (f : End X) : α.symm.c
onj (α.conj f) = f
-/
theorem self_symm_conj (f : End Y) : α.conj (α.symm.conj f) = f :=
  α.symm.symm_self_conj f

@[simp]
/-
**CategoryTheory.Iso.conj_pow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：conj_pow (f : End X) (n : Nat) : α.conj (f ^ n) = α.conj f ^ n
参数：f : End X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem conj_pow (f : End X) (n : ℕ) : α.conj (f ^ n) = α.conj f ^ n :=
  α.conj.toMonoidHom.map_pow f n

-- TODO: change definition so that `conjAut_apply` becomes a `rfl`?
/-- `conj` defines a group isomorphism between groups of automorphisms -/
/-
**CategoryTheory.Iso.conjAut** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：conjAut : Aut X ≃* Aut Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`conj` defines a group isomorphism between groups of automorphisms
-/
def conjAut : Aut X ≃* Aut Y :=
  (Aut.unitsEndEquivAut X).symm.trans <| (Units.mapEquiv α.conj).trans <| Aut.unitsEndEquivAut Y
/-
**CategoryTheory.Iso.conjAut_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso
`。
形式化陈述：conjAut_apply (f : Aut X) : α.conjAut f = α.symm ≪≫ f ≪≫ α
参数：f : Aut X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Aut.ext`：ext {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom
) : φ₁ = φ₂
-/
theorem conjAut_apply (f : Aut X) : α.conjAut f = α.symm ≪≫ f ≪≫ α := by cat_disch

@[simp]
/-
**CategoryTheory.Iso.conjAut_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：conjAut_hom (f : Aut X) : (α.conjAut f).hom = α.conj f.hom
参数：f : Aut X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjAut_hom (f : Aut X) : (α.conjAut f).hom = α.conj f.hom :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Iso.trans_conjAut** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso
`。
形式化陈述：trans_conjAut {Z : C} (β : Y ≅ Z) (f : Aut X) : (α ≪≫ β).conjAut f = β.con
jAut (α.conjAut f)
参数：β : Y ≅ Z；f : Aut X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.conjAut_apply`：conjAut_apply (f : Aut X) : α.conjAut 
f = α.symm ≪≫ f ≪≫ α
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_conjAut {Z : C} (β : Y ≅ Z) (f : Aut X) :
    (α ≪≫ β).conjAut f = β.conjAut (α.conjAut f) := by
  simp only [conjAut_apply, Iso.trans_symm, Iso.trans_assoc]

@[simp]
/-
**CategoryTheory.Iso.conjAut_mul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：conjAut_mul (f g : Aut X) : α.conjAut (f * g) = α.conjAut f * α.conjAut g
参数：f g : Aut X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem conjAut_mul (f g : Aut X) : α.conjAut (f * g) = α.conjAut f * α.conjAut g :=
  map_mul α.conjAut f g

@[simp]
/-
**CategoryTheory.Iso.conjAut_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso
`。
形式化陈述：conjAut_trans (f g : Aut X) : α.conjAut (f ≪≫ g) = α.conjAut f ≪≫ α.conjAu
t g
参数：f g : Aut X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.conjAut_mul`：conjAut_mul (f g : Aut X) : α.conjAut (f
 * g) = α.conjAut f * α.conjAut g
-/
theorem conjAut_trans (f g : Aut X) : α.conjAut (f ≪≫ g) = α.conjAut f ≪≫ α.conjAut g :=
  conjAut_mul α g f

@[simp]
/-
**CategoryTheory.Iso.conjAut_pow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：conjAut_pow (f : Aut X) (n : Nat) : α.conjAut (f ^ n) = α.conjAut f ^ n
参数：f : Aut X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem conjAut_pow (f : Aut X) (n : ℕ) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  map_pow α.conjAut f n

@[simp]
/-
**CategoryTheory.Iso.conjAut_zpow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`
。
形式化陈述：conjAut_zpow (f : Aut X) (n : Int) : α.conjAut (f ^ n) = α.conjAut f ^ n
参数：f : Aut X；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem conjAut_zpow (f : Aut X) (n : ℤ) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  map_zpow α.conjAut f n

end Iso

namespace Functor

universe v₁ u₁

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D)

/-
**CategoryTheory.Functor.map_conj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：map_conj {X Y : C} (α : X ≅ Y) (f : End X) : F.map (α.conj f) = (F.mapIso 
α).conj (F.map f)
参数：α : X ≅ Y；f : End X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_homCongr`：map_homCongr {X Y X₁ Y₁ : C} (α : X
 ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y) : F.map (Iso.homCongr α β f) = Iso.homCongr (F.m
apIso α) (F.mapIso β) (F.…
-/
theorem map_conj {X Y : C} (α : X ≅ Y) (f : End X) :
    F.map (α.conj f) = (F.mapIso α).conj (F.map f) :=
  map_homCongr F α α f

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.map_conjAut** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：map_conjAut (F : C ⥤ D) {X Y : C} (α : X ≅ Y) (f : Aut X) : F.mapIso (α.co
njAut f) = (F.mapIso α).conjAut (F.mapIso f)
参数：F : C ⥤ D；α : X ≅ Y；f : Aut X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_conj`：map_conj {X Y : C} (α : X ≅ Y) (f : End
 X) : F.map (α.conj f) = (F.mapIso α).conj (F.map f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_conjAut (F : C ⥤ D) {X Y : C} (α : X ≅ Y) (f : Aut X) :
    F.mapIso (α.conjAut f) = (F.mapIso α).conjAut (F.mapIso f) := by
  ext; simp only [mapIso_hom, Iso.conjAut_hom, F.map_conj]

-- alternative proof: by simp only [Iso.conjAut_apply, F.mapIso_trans, F.mapIso_symm]
end Functor

end CategoryTheory

