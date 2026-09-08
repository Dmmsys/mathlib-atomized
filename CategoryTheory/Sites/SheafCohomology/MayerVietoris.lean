/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The Mayer-Vietoris exact sequence in sheaf cohomology

Let `C` be a category equipped with a Grothendieck topology `J`.
Let `S : J.MayerVietorisSquare` be a Mayer-Vietoris square for `J`.
Let `F` be an abelian sheaf on `(C, J)`.

In this file, we obtain a long exact Mayer-Vietoris sequence:

`... ⟶ H^n(S.X₄, F) ⟶ H^n(S.X₂, F) ⊞ H^n(S.X₃, F) ⟶ H^n(S.X₁, F) ⟶ H^{n + 1}(S.X₄, F) ⟶ ...`

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Opposite Limits Abelian

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

namespace GrothendieckTopology.MayerVietorisSquare

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

/-- The sum of two restriction maps in sheaf cohomology. -/
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：toBiprod (n : Nat) : F.H' n S.X₄ ⟶ F.H' n S.X₂ ⊞ F.H' n S.X₃
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two restriction maps in sheaf cohomology.
-/
noncomputable def toBiprod (n : ℕ) :
    F.H' n S.X₄ ⟶ F.H' n S.X₂ ⊞ F.H' n S.X₃ :=
  biprod.lift ((F.cohomologyPresheaf n).map S.f₂₄.op)
      ((F.cohomologyPresheaf n).map S.f₃₄.op)
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_apply** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：toBiprod_apply {n : Nat} (y : F.H' n S.X₄) : S.toBiprod F n y = (AddCommGr
pCat.biprodIsoProd _ _).inv ⟨(F.cohomologyPresheaf n).map S.f₂₄.op y, (F.cohomol
ogyPresheaf n).map S.f₃₄.op y⟩
参数：y : F.H' n S.X₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `AddCommGrpCat.instHasBinaryBiproducts`：CategoryTheory.Limits.HasBinaryBi
products AddCommGrpCat
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.addCommGroupIsoToAddEquiv_apply`：∀ {X Y : AddCommGrpC
at} (i : X ≅ Y) (a : ↑X), i.addCommGroupIsoToAddEquiv a = (AddCommGrpCat.Hom.hom
 i.hom) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply`：∀ (G H : AddCommGrpCat) 
(x : ↑G × ↑H),   (CategoryTheory.ConcreteCategory.hom CategoryTheory.Limits.bipr
od.fst)       ((CategoryTheory.Concr…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `AddCommGrpCat.biprodIsoProd_inv_comp_snd_apply`：∀ (G H : AddCommGrpCat) 
(x : ↑G × ↑H),   (CategoryTheory.ConcreteCategory.hom CategoryTheory.Limits.bipr
od.snd)       ((CategoryTheory.Concr…
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
lemma toBiprod_apply {n : ℕ} (y : F.H' n S.X₄) :
    S.toBiprod F n y = (AddCommGrpCat.biprodIsoProd _ _).inv
      ⟨(F.cohomologyPresheaf n).map S.f₂₄.op y,
        (F.cohomologyPresheaf n).map S.f₃₄.op y⟩ := by
  apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
  dsimp [toBiprod]
  ext
  · rw [Iso.addCommGroupIsoToAddEquiv_apply,
      Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply,
      Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply,
      biprod.lift_fst, Iso.inv_hom_id_apply]
  · rw [Iso.addCommGroupIsoToAddEquiv_apply,
      Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_snd_apply,
      Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply,
      biprod.lift_snd, Iso.inv_hom_id_apply]

/-- The difference of two restriction maps in sheaf cohomology. -/
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：fromBiprod (n : Nat) : F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₁
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The difference of two restriction maps in sheaf cohomology.
-/
noncomputable def fromBiprod (n : ℕ) :
    F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₁ :=
  biprod.desc ((F.cohomologyPresheaf n).map S.f₁₂.op)
      (-(F.cohomologyPresheaf n).map S.f₁₃.op)

@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_fromBiprod** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare
`。
形式化陈述：toBiprod_fromBiprod (n : Nat) : S.toBiprod F n ≫ S.fromBiprod F n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `AddCommGrpCat.instHasBinaryBiproducts`：CategoryTheory.Limits.HasBinaryBi
products AddCommGrpCat
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {X Y : C}   [in
st_2 : CategoryTheory.Limits…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Square.fac`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] (self : CategoryTheory.Square C),   CategoryTheory.CategoryStruct.co
mp self.f₁₂ sel…
· 使用定理 `CategoryTheory.Preadditive.comp_neg`：comp_neg : f ≫ (-g) = -f ≫ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toBiprod_fromBiprod (n : ℕ) : S.toBiprod F n ≫ S.fromBiprod F n = 0 := by
  simp only [toBiprod, fromBiprod, biprod.lift_desc, Preadditive.comp_neg,
    ← sub_eq_add_neg, sub_eq_zero, ← Functor.map_comp, ← op_comp, S.toSquare.fac]
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoPr
od_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.Maye
rVietorisSquare`。
形式化陈述：fromBiprod_biprodIsoProd_inv_apply {n : Nat} (y₁ : F.H' n S.X₂) (y₂ : F.H'
 n S.X₃) : S.fromBiprod F n ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨y₁, y₂⟩) = (
F.cohomologyPresheaf n).map S.f₁₂.op y₁ - (F.cohomologyPresheaf n).map S.f₁₃.op 
y₂
参数：y₁ : F.H' n S.X₂；y₂ : F.H' n S.X₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `AddCommGrpCat.instHasBinaryBiproducts`：CategoryTheory.Limits.HasBinaryBi
products AddCommGrpCat
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AddCommGrpCat.biprodIsoProd_inv_comp_desc`：biprodIsoProd_inv_comp_desc {
G H K : AddCommGrpCat.{u}} (f : G ⟶ K) (g : H ⟶ K) : (biprodIsoProd G H).inv ≫ b
iprod.desc f g = ofHom (AddMono…
· 使用定理 `CategoryTheory.Preadditive.comp_neg`：comp_neg : f ≫ (-g) = -f ≫ g
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromBiprod_biprodIsoProd_inv_apply {n : ℕ}
    (y₁ : F.H' n S.X₂) (y₂ : F.H' n S.X₃) :
    S.fromBiprod F n ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨y₁, y₂⟩) =
      (F.cohomologyPresheaf n).map S.f₁₂.op y₁ - (F.cohomologyPresheaf n).map S.f₁₃.op y₂ := by
  dsimp [fromBiprod]
  rw [← ConcreteCategory.comp_apply]
  simp [AddCommGrpCat.biprodIsoProd_inv_comp_desc, sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] toBiprod_apply in
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.biprodAddEquiv_symm_bi
prodIsoProd_hom_toBiprod_apply** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grothen
dieckTopology.MayerVietorisSquare`。
形式化陈述：biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply {n : Nat} (x : F.H' n
 S.X₄) : Ext.biprodAddEquiv.symm ((AddCommGrpCat.biprodIsoProd _ _).hom (S.toBip
rod F n x)) = (Ext.mk₀ S.shortComplex.g).comp x (zero_add n)
参数：x : F.H' n S.X₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `AddCommGrpCat.instHasBinaryBiproducts`：CategoryTheory.Limits.HasBinaryBi
products AddCommGrpCat
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_apply`：
toBiprod_apply {n : Nat} (y : F.H' n S.X₄) : S.toBiprod F n y = (AddCommGrpCat.b
iprodIsoProd _ _).inv ⟨(F.cohomologyPresheaf n).map S.f₂₄.op…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {F : C → C → Type uF}   {carrier 
: C → Type w} {instFunLik…
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `CategoryTheory.Abelian.Ext.comp.congr_simp`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Cat
egoryTheory.HasExt C] {X Y Z : C…
· 使用定理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_g`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Gro
thendieckTopology C}   [inst_1 : CategoryTheory.HasWeakSheaf…
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `CategoryTheory.Abelian.Ext.biprodAddEquiv_apply_fst`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [ins
t_2 : CategoryTheory.HasExt C] {X₁ X₂ Y :…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc`：mk₀_comp_mk₀_assoc (f : X
 ⟶ Y) (g : Y ⟶ Z) {n : Nat} (α : Ext Z T n) : (mk₀ f).comp ((mk₀ g).comp α (zero
_add n)) (zero_add n) = (mk₀ (f ≫ g…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Abelian.Ext.biprodAddEquiv_apply_snd`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [ins
t_2 : CategoryTheory.HasExt C] {X₁ X₂ Y :…
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
lemma biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply
    {n : ℕ} (x : F.H' n S.X₄) :
    Ext.biprodAddEquiv.symm ((AddCommGrpCat.biprodIsoProd _ _).hom (S.toBiprod F n x)) =
      (Ext.mk₀ S.shortComplex.g).comp x (zero_add n) :=
  Ext.biprodAddEquiv.injective (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] sub_eq_add_neg in
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.mk** 是 Mathlib 中的一个cto
r，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Cate
goryTheory.GrothendieckTopology C} →       [inst_1 : CategoryTheory.HasWeakSheaf
ify J (Type v)] →         (toSquare : CategoryTheory.Square C) →           autoP
aram (CategoryTheory.Mono toSquare.f₁₃)               CategoryTheory.Grothendiec
kTopology.MayerVietorisSquare.mono_f₁₃._autoParam →             (toSquare.map (C
ategoryTheory.yoneda.comp (CategoryTheory.presheafToSheaf J (Type v)))).IsPushou
t →               J.MayerVietorisSquare
参数：Type v；toSquare : CategoryTheory.Square C；CategoryTheory.Mono toSquare.f₁₃；to
Square.map (CategoryTheory.yoneda.comp (CategoryTheory.presheafToSheaf J (Type v
)))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom
    {n : ℕ} (x : ↑(F.H' n S.X₂ ⊞ F.H' n S.X₃)) :
    (Ext.mk₀ S.shortComplex.f).comp
      (Ext.biprodAddEquiv.symm ((AddCommGrpCat.biprodIsoProd _ _).hom x)) (zero_add n) =
    (S.fromBiprod F n x) := by
  obtain ⟨⟨x₂, x₃⟩, rfl⟩ :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective x
  dsimp
  rw [Ext.biprodAddEquiv_symm_apply,
    Iso.addCommGroupIsoToAddEquiv_symm_apply,
    fromBiprod_biprodIsoProd_inv_apply]
  cat_disch

variable (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

/-- The connecting homomorphism of the Mayer-Vietoris long exact sequence
in sheaf cohomology. -/
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism of the Mayer-Vietoris long exact sequence
in sheaf cohomology.
-/
noncomputable def δ :
    F.H' n₀ S.X₁ ⟶ F.H' n₁ S.X₄ :=
  AddCommGrpCat.ofHom (S.shortComplex_shortExact.extClass.precomp _ (by omega))

open ComposableArrows

/-- The Mayer-Vietoris long exact sequence of an abelian sheaf `F : Sheaf J AddCommGrpCat`
for a Mayer-Vietoris square `S : J.MayerVietorisSquare`. -/
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence** 是 Mathlib 中
的一个缩写定义，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：sequence : ComposableArrows AddCommGrpCat.{w} 5
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Mayer-Vietoris long exact sequence of an abelian sheaf `F : Sheaf J AddCommG
rpCat`
for a Mayer-Vietoris square `S : J.MayerVietorisSquare`.
-/
noncomputable abbrev sequence : ComposableArrows AddCommGrpCat.{w} 5 :=
  mk₅ (S.toBiprod F n₀) (S.fromBiprod F n₀) (S.δ F n₀ n₁ h)
    (S.toBiprod F n₁) (S.fromBiprod F n₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Comparison isomorphism from the Mayer-Vietoris sequence and the
contravariant sequence of `Ext`-groups. -/
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequenceIso** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：sequenceIso : S.sequence F n₀ n₁ h ≅ Ext.contravariantSequence S.shortComp
lex_shortExact F n₀ n₁ (by omega)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_sho
rtExact`：shortComplex_shortExact : S.shortComplex.ShortExact where exact
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…

--- 原说明 ---
Comparison isomorphism from the Mayer-Vietoris sequence and the
contravariant sequence of `Ext`-groups.
-/
noncomputable def sequenceIso : S.sequence F n₀ n₁ h ≅
    Ext.contravariantSequence S.shortComplex_shortExact F n₀ n₁ (by omega) :=
  isoMk₅ (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _) (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _)
    (by ext; apply biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom)
    (by dsimp; rw [comp_id, id_comp]; rfl)
    (by ext; apply biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom)
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
形式化陈述：sequence_exact : (S.sequence F n₀ n₁ h).Exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.exact_of_iso`：exact_of_iso {S₁ S₂ : Comp
osableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.Exact) : S₂.Exact where toIsComplex
· 使用引理 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_sho
rtExact`：shortComplex_shortExact : S.shortComplex.ShortExact where exact
· 使用引理 `CategoryTheory.Abelian.Ext.contravariantSequence_exact`：contravariantSeq
uence_exact : (contravariantSequence hS Y n₀ n₁ h).Exact
-/
lemma sequence_exact : (S.sequence F n₀ n₁ h).Exact :=
  exact_of_iso (S.sequenceIso F n₀ n₁ h).symm (Ext.contravariantSequence_exact _ _ _ _ _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_toBiprod : S.δ F n₀ n₁ h ≫ S.toBiprod F n₁ = 0 :=
  (S.sequence_exact F n₀ n₁ h).zero 2

@[reassoc (attr := simp)]
/-
**CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.MayerVietorisSquare`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromBiprod_δ : S.fromBiprod F n₀ ≫ S.δ F n₀ n₁ h = 0 :=
  (S.sequence_exact F n₀ n₁ h).zero 1

end GrothendieckTopology.MayerVietorisSquare

end CategoryTheory

