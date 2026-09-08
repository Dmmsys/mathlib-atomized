/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sophie Morel
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.DFinsupp.Small
public import Mathlib.GroupTheory.QuotientGroup.Defs
/-!
# The category of additive commutative groups has all colimits.

This file constructs colimits in the category of additive commutative groups, as
quotients of finitely supported functions.

-/

@[expose] public section

universe u' w u v

open CategoryTheory Limits

namespace AddCommGrpCat

variable {J : Type u} [Category.{v} J] (F : J ⥤ AddCommGrpCat.{w})

namespace Colimits

/-!
We build the colimit of a diagram in `AddCommGrpCat` by constructing the
free group on the disjoint union of all the abelian groups in the diagram,
then taking the quotient by the abelian group laws within each abelian group,
and the identifications given by the morphisms in the diagram.
-/

/--
The relations between elements of the direct sum of the `F.obj j` given by the
morphisms in the diagram `J`.
-/
/-
**AddCommGrpCat.Colimits.Relations** 是 Mathlib 中的一个缩写定义，位于命名空间 `AddCommGrpCat.Co
limits`。
形式化陈述：Relations [DecidableEq J] : AddSubgroup (DFinsupp (fun j => F.obj j))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relations between elements of the direct sum of the `F.obj j` given by the
morphisms in the diagram `J`.
-/
abbrev Relations [DecidableEq J] : AddSubgroup (DFinsupp (fun j ↦ F.obj j)) :=
  AddSubgroup.closure {x | ∃ (j j' : J) (u : j ⟶ j') (a : F.obj j),
    x = DFinsupp.single j' (F.map u a) - DFinsupp.single j a}

/--
The candidate for the colimit of `F`, defined as the quotient of the direct sum
of the commutative groups `F.obj j` by the relations given by the morphisms in
the diagram.
-/
/-
**AddCommGrpCat.Colimits.Quot** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat.Colimits`
。
形式化陈述：Quot [DecidableEq J] : Type (max u w)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The candidate for the colimit of `F`, defined as the quotient of the direct sum
of the commutative groups `F.obj j` by the relations given by the morphisms in
the diagram.
-/
def Quot [DecidableEq J] : Type (max u w) :=
  DFinsupp (fun j ↦ F.obj j) ⧸ Relations F
/-
**AddCommGrpCat.Colimits.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat.Colimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq J] : AddCommGroup (Quot F) :=
  QuotientAddGroup.Quotient.addCommGroup (Relations F)

/-- Inclusion of `F.obj j` into the candidate colimit.
-/
/-
**AddCommGrpCat.Colimits.Quot.** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat.Colimits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inclusion of `F.obj j` into the candidate colimit.
-/
def Quot.ι [DecidableEq J] (j : J) : F.obj j →+ Quot F :=
  (QuotientAddGroup.mk' _).comp (DFinsupp.singleAddHom (fun j ↦ F.obj j) j)
/-
**AddCommGrpCat.Colimits.Quot.addMonoidHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `AddCom
mGrpCat.Colimits.Quot`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] (F : CategoryTheo
ry.Functor J AddCommGrpCat)   [inst_1 : DecidableEq J] {α : Type u_1} [inst_2 : 
AddMonoid α] {f g : AddCommGrpCat.Colimits.Quot F →+ α},   (∀ (j : J) (x : ↑(F.o
bj j)), f ((AddCommGrpCat.Colimits.Quot.ι F j) x) = g ((AddCommGrpCat.Colimits.Q
uot.ι F j) x)) →     f = g
参数：F : CategoryTheory.Functor J AddCommGrpCat；∀ (j : J) (x : ↑(F.obj j)), f ((Ad
dCommGrpCat.Colimits.Quot.ι F j) x) = g ((AddCommGrpCat.Colimits.Quot.ι F j) x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.addMonoidHom_ext`：∀ {G : Type u_1} {M : Type u_4} [inst
 : AddGroup G] [inst_1 : AddMonoid M] (N : AddSubgroup G) [nN : N.Normal]   ⦃f g
 : G ⧸ N →+ M⦄, f.comp …
· 使用定理 `DFinsupp.addHom_ext`：addHom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀
 i, β i) ->+ γ⦄ (H : forall (i : ι) (y : β i), f (single i y) = g (single i y)) 
: f = g
-/
lemma Quot.addMonoidHom_ext [DecidableEq J] {α : Type*} [AddMonoid α] {f g : Quot F →+ α}
    (h : ∀ (j : J) (x : F.obj j), f (Quot.ι F j x) = g (Quot.ι F j x)) : f = g :=
  QuotientAddGroup.addMonoidHom_ext _ (DFinsupp.addHom_ext h)

variable (c : Cocone F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (implementation detail) Part of the universal property of the colimit cocone, but without
assuming that `Quot F` lives in the correct universe. -/
/-
**AddCommGrpCat.Colimits.Quot.desc** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat.Coli
mits.Quot`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     (F : Cate
goryTheory.Functor J AddCommGrpCat) →       (c : CategoryTheory.Limits.Cocone F)
 → [inst_1 : DecidableEq J] → AddCommGrpCat.Colimits.Quot F →+ ↑c.pt
参数：F : CategoryTheory.Functor J AddCommGrpCat；c : CategoryTheory.Limits.Cocone F
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation detail) Part of the universal property of the colimit cocone, bu
t without
assuming that `Quot F` lives in the correct universe.
-/
def Quot.desc [DecidableEq J] : Quot.{w} F →+ c.pt := by
  refine QuotientAddGroup.lift _ (DFinsupp.sumAddHom fun x => (c.ι.app x).hom) ?_
  dsimp
  rw [AddSubgroup.closure_le]
  intro _ ⟨_, _, _, _, eq⟩
  rw [eq]
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, DFinsupp.sumAddHom_single]
  change (F.map _ ≫ c.ι.app _) _ - _ = 0
  rw [c.ι.naturality]
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, sub_self]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AddCommGrpCat.Colimits.Quot.** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGrpCat.Colimits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Quot.ι_desc [DecidableEq J] (j : J) (x : F.obj j) :
    Quot.desc F c (Quot.ι F j x) = c.ι.app j x := by
  dsimp [desc, ι]
  erw [QuotientAddGroup.lift_mk']
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AddCommGrpCat.Colimits.Quot.map_** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGrpCat.Coli
mits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Quot.map_ι [DecidableEq J] {j j' : J} {f : j ⟶ j'} (x : F.obj j) :
    Quot.ι F j' (F.map f x) = Quot.ι F j x := by
  dsimp [ι]
  refine eq_of_sub_eq_zero ?_
  erw [← (QuotientAddGroup.mk' (Relations F)).map_sub, ← AddMonoidHom.mem_ker]
  rw [QuotientAddGroup.ker_mk']
  simp only [DFinsupp.singleAddHom_apply]
  exact AddSubgroup.subset_closure ⟨j, j', f, x, rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The obvious additive map from `Quot F` to `Quot (F ⋙ uliftFunctor.{u'})`.
-/
/-
**AddCommGrpCat.Colimits.quotToQuotUlift** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCa
t.Colimits`。
形式化陈述：quotToQuotUlift [DecidableEq J] : Quot F ->+ Quot (F ⋙ uliftFunctor.{u'})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious additive map from `Quot F` to `Quot (F ⋙ uliftFunctor.{u'})`.
-/
def quotToQuotUlift [DecidableEq J] : Quot F →+ Quot (F ⋙ uliftFunctor.{u'}) := by
  refine QuotientAddGroup.lift (Relations F) (DFinsupp.sumAddHom (fun j ↦ (Quot.ι _ j).comp
    AddEquiv.ulift.symm.toAddMonoidHom)) ?_
  rw [AddSubgroup.closure_le]
  intro _ hx
  obtain ⟨j, j', u, a, rfl⟩ := hx
  rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, DFinsupp.sumAddHom_single,
    DFinsupp.sumAddHom_single]
  change Quot.ι (F ⋙ uliftFunctor) j' ((F ⋙ uliftFunctor).map u (AddEquiv.ulift.symm a)) - _ = _
  rw [Quot.map_ι]
  dsimp
  rw [sub_self]
/-
**AddCommGrpCat.Colimits.quotToQuotUlift_** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGrpC
at.Colimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotToQuotUlift_ι [DecidableEq J] (j : J) (x : F.obj j) :
    quotToQuotUlift F (Quot.ι F j x) = Quot.ι _ j (ULift.up x) := by
  dsimp [quotToQuotUlift, Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations F))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply, DFinsupp.sumAddHom_single]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
The obvious additive map from `Quot (F ⋙ uliftFunctor.{u'})` to `Quot F`.
-/
/-
**AddCommGrpCat.Colimits.quotUliftToQuot** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCa
t.Colimits`。
形式化陈述：quotUliftToQuot [DecidableEq J] : Quot (F ⋙ uliftFunctor.{u'}) ->+ Quot F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious additive map from `Quot (F ⋙ uliftFunctor.{u'})` to `Quot F`.
-/
def quotUliftToQuot [DecidableEq J] : Quot (F ⋙ uliftFunctor.{u'}) →+ Quot F := by
  refine QuotientAddGroup.lift (Relations (F ⋙ uliftFunctor))
    (DFinsupp.sumAddHom (fun j ↦ (Quot.ι _ j).comp AddEquiv.ulift.toAddMonoidHom)) ?_
  rw [AddSubgroup.closure_le]
  intro _ hx
  obtain ⟨j, j', u, a, rfl⟩ := hx
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**AddCommGrpCat.Colimits.quotUliftToQuot_** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGrpC
at.Colimits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotUliftToQuot_ι [DecidableEq J] (j : J) (x : (F ⋙ uliftFunctor.{u'}).obj j) :
    quotUliftToQuot F (Quot.ι _ j x) = Quot.ι F j x.down := by
  dsimp [quotUliftToQuot, Quot.ι]
  conv_lhs => erw [AddMonoidHom.comp_apply (QuotientAddGroup.mk' (Relations (F ⋙ uliftFunctor)))
    (DFinsupp.singleAddHom _ j), QuotientAddGroup.lift_mk']
  simp only [DFinsupp.singleAddHom_apply,
    DFinsupp.sumAddHom_single, AddMonoidHom.coe_comp, Function.comp_apply]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
The additive equivalence between `Quot F` and `Quot (F ⋙ uliftFunctor.{u'})`.
-/
@[simp]
/-
**AddCommGrpCat.Colimits.quotQuotUliftAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddCom
mGrpCat.Colimits`。
形式化陈述：quotQuotUliftAddEquiv [DecidableEq J] : Quot F ≃+ Quot (F ⋙ uliftFunctor.{
u'}) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence between `Quot F` and `Quot (F ⋙ uliftFunctor.{u'})`.
-/
def quotQuotUliftAddEquiv [DecidableEq J] : Quot F ≃+ Quot (F ⋙ uliftFunctor.{u'}) where
  toFun := quotToQuotUlift F
  invFun := quotUliftToQuot F
  left_inv x := by
    conv_rhs => rw [← AddMonoidHom.id_apply _ x]
    rw [← AddMonoidHom.comp_apply, Quot.addMonoidHom_ext F (f := (quotUliftToQuot F).comp
      (quotToQuotUlift F)) (fun j a ↦ ?_)]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, quotToQuotUlift_ι, quotUliftToQuot_ι]
  right_inv x := by
    conv_rhs => rw [← AddMonoidHom.id_apply _ x]
    rw [← AddMonoidHom.comp_apply, Quot.addMonoidHom_ext _ (f := (quotToQuotUlift F).comp
      (quotUliftToQuot F)) (fun j a ↦ ?_)]
    rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, quotUliftToQuot_ι, quotToQuotUlift_ι]
    rfl
  map_add' _ _ := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AddCommGrpCat.Colimits.Quot.desc_quotQuotUliftAddEquiv** 是 Mathlib 中的一个定理，位于命名
空间 `AddCommGrpCat.Colimits.Quot`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] (F : CategoryTheo
ry.Functor J AddCommGrpCat)   [inst_1 : DecidableEq J] (c : CategoryTheory.Limit
s.Cocone F),   (AddCommGrpCat.Colimits.Quot.desc (F.comp AddCommGrpCat.uliftFunc
tor) (AddCommGrpCat.uliftFunctor.mapCocone c)).comp       (AddCommGrpCat.Colimit
s.quotQuotUliftAddEquiv F).toAddMonoidHom =     AddEquiv.ulift.symm.toAddMonoidH
om.comp (AddCommGrpCat.Colimits.Quot.desc F c)
参数：F : CategoryTheory.Functor J AddCommGrpCat；c : CategoryTheory.Limits.Cocone F
；AddCommGrpCat.Colimits.Quot.desc (F.comp AddCommGrpCat.uliftFunctor) (AddCommGr
pCat.uliftFunctor.mapCocone c)；AddCommGrpCat.Colimits.quotQuotUliftAddEquiv F；Ad
dCommGrpCat.Colimits.Quot.desc F c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.Colimits.Quot.addMonoidHom_ext`：∀ {J : Type u} [inst : Cat
egoryTheory.Category.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [i
nst_1 : DecidableEq J] {α : Type u…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddCommGrpCat.Colimits.quotToQuotUlift_ι`：quotToQuotUlift_ι [DecidableEq
 J] (j : J) (x : F.obj j) : quotToQuotUlift F (Quot.ι F j x) = Quot.ι _ j (ULift
.up x)
· 使用定理 `AddCommGrpCat.Colimits.Quot.ι_desc`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   (c : Categor
yTheory.Limits.Cocone F)…
-/
lemma Quot.desc_quotQuotUliftAddEquiv [DecidableEq J] (c : Cocone F) :
    (Quot.desc (F ⋙ uliftFunctor.{u'}) (uliftFunctor.{u'}.mapCocone c)).comp
    (quotQuotUliftAddEquiv F).toAddMonoidHom =
    AddEquiv.ulift.symm.toAddMonoidHom.comp (Quot.desc F c) := by
  refine Quot.addMonoidHom_ext _ (fun j a ↦ ?_)
  dsimp
  simp only [quotToQuotUlift_ι, Functor.comp_obj, uliftFunctor_obj, ι_desc, Functor.const_obj_obj,
    ι_desc]
  erw [Quot.ι_desc]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- (implementation detail) A morphism of commutative additive groups `Quot F →+ A`
induces a cocone on `F` as long as the universes work out.
-/
@[simps]
/-
**AddCommGrpCat.Colimits.toCocone** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat.Colim
its`。
形式化陈述：toCocone [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F ->+ A) 
: Cocone F where pt
参数：f : Quot F ->+ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation detail) A morphism of commutative additive groups `Quot F →+ A`
induces a cocone on `F` as long as the universes work out.
-/
def toCocone [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F →+ A) : Cocone F where
  pt := AddCommGrpCat.of A
  ι.app j := ofHom <| f.comp (Quot.ι F j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AddCommGrpCat.Colimits.Quot.desc_toCocone_desc** 是 Mathlib 中的一个定理，位于命名空间 `AddC
ommGrpCat.Colimits.Quot`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] (F : CategoryTheo
ry.Functor J AddCommGrpCat)   (c : CategoryTheory.Limits.Cocone F) [inst_1 : Dec
idableEq J] {A : Type w} [inst_2 : AddCommGroup A]   (f : AddCommGrpCat.Colimits
.Quot F →+ A) (hc : CategoryTheory.Limits.IsColimit c),   (AddCommGrpCat.Hom.hom
 (hc.desc (AddCommGrpCat.Colimits.toCocone F f))).comp (AddCommGrpCat.Colimits.Q
uot.desc F c) =     f
参数：F : CategoryTheory.Functor J AddCommGrpCat；c : CategoryTheory.Limits.Cocone F
；f : AddCommGrpCat.Colimits.Quot F →+ A；hc : CategoryTheory.Limits.IsColimit c；A
ddCommGrpCat.Hom.hom (hc.desc (AddCommGrpCat.Colimits.toCocone F f))；AddCommGrpC
at.Colimits.Quot.desc F c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.Colimits.Quot.addMonoidHom_ext`：∀ {J : Type u} [inst : Cat
egoryTheory.Category.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [i
nst_1 : DecidableEq J] {α : Type u…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.comp_apply`：∀ {M : Type u_4} {N : Type u_5} {P : Type u_6} 
[inst : AddZero M] [inst_1 : AddZero N] [inst_2 : AddZero P] (g : N →+ P)   (f :
 M →+ N) (x :…
· 使用定理 `AddCommGrpCat.Colimits.Quot.ι_desc`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   (c : Categor
yTheory.Limits.Cocone F)…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Quot.desc_toCocone_desc [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F →+ A)
    (hc : IsColimit c) : (hc.desc (toCocone F f)).hom.comp (Quot.desc F c) = f := by
  refine Quot.addMonoidHom_ext F (fun j x ↦ ?_)
  rw [AddMonoidHom.comp_apply, ι_desc]
  change (c.ι.app j ≫ hc.desc (toCocone F f)) _ = _
  rw [hc.fac]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AddCommGrpCat.Colimits.Quot.desc_toCocone_desc_app** 是 Mathlib 中的一个定理，位于命名空间 `
AddCommGrpCat.Colimits.Quot`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] (F : CategoryTheo
ry.Functor J AddCommGrpCat)   (c : CategoryTheory.Limits.Cocone F) [inst_1 : Dec
idableEq J] {A : Type w} [inst_2 : AddCommGroup A]   (f : AddCommGrpCat.Colimits
.Quot F →+ A) (hc : CategoryTheory.Limits.IsColimit c) (x : AddCommGrpCat.Colimi
ts.Quot F),   (CategoryTheory.ConcreteCategory.hom (hc.desc (AddCommGrpCat.Colim
its.toCocone F f)))       ((AddCommGrpCat.Colimits.Quot.desc F c) x) =     f x
参数：F : CategoryTheory.Functor J AddCommGrpCat；c : CategoryTheory.Limits.Cocone F
；f : AddCommGrpCat.Colimits.Quot F →+ A；hc : CategoryTheory.Limits.IsColimit c；x
 : AddCommGrpCat.Colimits.Quot F；CategoryTheory.ConcreteCategory.hom (hc.desc (A
ddCommGrpCat.Colimits.toCocone F f))；(AddCommGrpCat.Colimits.Quot.desc F c) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddCommGrpCat.Colimits.Quot.desc_toCocone_desc`：∀ {J : Type u} [inst : C
ategoryTheory.Category.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   
(c : CategoryTheory.Limits.Cocone F)…
-/
lemma Quot.desc_toCocone_desc_app [DecidableEq J] {A : Type w} [AddCommGroup A] (f : Quot F →+ A)
    (hc : IsColimit c) (x : Quot F) : hc.desc (toCocone F f) (Quot.desc F c x) = f x := by
  conv_rhs => rw [← Quot.desc_toCocone_desc F c f hc]
  dsimp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
If `c` is a cocone of `F` such that `Quot.desc F c` is bijective, then `c` is a colimit
cocone of `F`.
-/
/-
**AddCommGrpCat.Colimits.isColimit_of_bijective_desc** 是 Mathlib 中的一个定义，位于命名空间 `
AddCommGrpCat.Colimits`。
形式化陈述：isColimit_of_bijective_desc [DecidableEq J] (h : Function.Bijective (Quot.
desc F c)) : IsColimit c where desc s
参数：h : Function.Bijective (Quot.desc F c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a cocone of `F` such that `Quot.desc F c` is bijective, then `c` is a 
colimit
cocone of `F`.
-/
noncomputable def isColimit_of_bijective_desc [DecidableEq J]
     (h : Function.Bijective (Quot.desc F c)) : IsColimit c where
  desc s := AddCommGrpCat.ofHom ((Quot.desc F s).comp (AddEquiv.ofBijective
    (Quot.desc F c) h).symm.toAddMonoidHom)
  fac s j := by
    ext x
    dsimp
    conv_lhs => erw [← Quot.ι_desc F c j x]
    rw [← AddEquiv.ofBijective_apply _ h, AddEquiv.symm_apply_apply]
    simp only [Quot.ι_desc, Functor.const_obj_obj]
  uniq s m hm := by
    ext x
    obtain ⟨x, rfl⟩ := h.2 x
    dsimp
    rw [← AddEquiv.ofBijective_apply _ h, AddEquiv.symm_apply_apply]
    suffices eq : m.hom.comp (AddEquiv.ofBijective (Quot.desc F c) h) = Quot.desc F s by
      rw [← eq]; rfl
    exact Quot.addMonoidHom_ext F (by simp [← hm])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (internal implementation) The colimit cocone of a functor `F`, implemented as a quotient of
`DFinsupp (fun j ↦ F.obj j)`, under the assumption that said quotient is small.
-/
@[simps pt ι_app]
/-
**AddCommGrpCat.Colimits.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat.
Colimits`。
形式化陈述：colimitCocone [DecidableEq J] [Small.{w} (Quot.{w} F)] : Cocone F where pt
参数：Quot.{w} F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(internal implementation) The colimit cocone of a functor `F`, implemented as a 
quotient of
`DFinsupp (fun j ↦ F.obj j)`, under the assumption that said quotient is small.
-/
noncomputable def colimitCocone [DecidableEq J] [Small.{w} (Quot.{w} F)] : Cocone F where
  pt := AddCommGrpCat.of (Shrink (Quot F))
  ι :=
    { app j :=
        AddCommGrpCat.ofHom (Shrink.addEquiv.symm.toAddMonoidHom.comp (Quot.ι F j))
      naturality _ _ _ := by
        ext
        dsimp
        change Shrink.addEquiv.symm _ = _
        rw [Quot.map_ι] }

@[simp]
/-
**AddCommGrpCat.Colimits.Quot.desc_colimitCocone** 是 Mathlib 中的一个定理，位于命名空间 `AddC
ommGrpCat.Colimits.Quot`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] [inst_1 : Decidab
leEq J]   (F : CategoryTheory.Functor J AddCommGrpCat) [inst_2 : Small.{w, max u
 w} (AddCommGrpCat.Colimits.Quot F)],   AddCommGrpCat.Colimits.Quot.desc F (AddC
ommGrpCat.Colimits.colimitCocone F) = Shrink.addEquiv.symm.toAddMonoidHom
参数：F : CategoryTheory.Functor J AddCommGrpCat；AddCommGrpCat.Colimits.Quot F；AddC
ommGrpCat.Colimits.colimitCocone F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommGrpCat.Colimits.Quot.addMonoidHom_ext`：∀ {J : Type u} [inst : Cat
egoryTheory.Category.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [i
nst_1 : DecidableEq J] {α : Type u…
· 使用定理 `AddCommGrpCat.Colimits.Quot.ι_desc`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   (c : Categor
yTheory.Limits.Cocone F)…
-/
theorem Quot.desc_colimitCocone [DecidableEq J] (F : J ⥤ AddCommGrpCat.{w}) [Small.{w} (Quot F)] :
    Quot.desc F (colimitCocone F) = (Shrink.addEquiv (α := Quot F)).symm.toAddMonoidHom := by
  refine Quot.addMonoidHom_ext F (fun j x ↦ ?_)
  simpa only [colimitCocone_pt, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    using! Quot.ι_desc F (colimitCocone F) j x

/-- (internal implementation) The fact that the candidate colimit cocone constructed in
`colimitCocone` is the colimit.
-/
/-
**AddCommGrpCat.Colimits.colimitCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `AddCo
mmGrpCat.Colimits`。
形式化陈述：colimitCoconeIsColimit [DecidableEq J] [Small.{w} (Quot F)] : IsColimit (c
olimitCocone F)
参数：Quot F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(internal implementation) The fact that the candidate colimit cocone constructed
 in
`colimitCocone` is the colimit.
-/
noncomputable def colimitCoconeIsColimit [DecidableEq J] [Small.{w} (Quot F)] :
    IsColimit (colimitCocone F) := by
  refine isColimit_of_bijective_desc F _ ?_
  rw [Quot.desc_colimitCocone]
  exact Shrink.addEquiv.symm.bijective

end Colimits

open Colimits

/-
**AddCommGrpCat.hasColimit_of_small_quot** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGrpCa
t`。
形式化陈述：hasColimit_of_small_quot [DecidableEq J] (h : Small.{w} (Quot F)) : HasCol
imit F
参数：h : Small.{w} (Quot F)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasColimit_of_small_quot [DecidableEq J] (h : Small.{w} (Quot F)) : HasColimit F :=
  ⟨_, colimitCoconeIsColimit F⟩
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq J] [Small.{w} J] : Small.{w} (Quot F) :=
  small_of_surjective (QuotientAddGroup.mk'_surjective _)
/-
**AddCommGrpCat.hasColimit** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
形式化陈述：hasColimit [Small.{w} J] (F : J ⥤ AddCommGrpCat.{w}) : HasColimit F
参数：F : J ⥤ AddCommGrpCat.{w}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AddCommGrpCat.hasColimit_of_small_quot`：hasColimit_of_small_quot [Decida
bleEq J] (h : Small.{w} (Quot F)) : HasColimit F
· 使用定理 `AddCommGrpCat.instSmallQuot`：∀ {J : Type u} [inst : CategoryTheory.Categ
ory.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [inst_1 : Decidable
Eq J] [Small.{w, …
-/
instance hasColimit [Small.{w} J] (F : J ⥤ AddCommGrpCat.{w}) : HasColimit F := by
  classical
  exact hasColimit_of_small_quot F inferInstance


/--
If `J` is `w`-small, then any functor `J ⥤ AddCommGrpCat.{w}` has a colimit.
-/
/-
**AddCommGrpCat.hasColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] [Small.{w, u} J],
   CategoryTheory.Limits.HasColimitsOfShape J AddCommGrpCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `J` is `w`-small, then any functor `J ⥤ AddCommGrpCat.{w}` has a colimit.
-/
instance hasColimitsOfShape [Small.{w} J] : HasColimitsOfShape J (AddCommGrpCat.{w}) where

/-- The category of additive commutative groups has all small colimits.
-/
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of additive commutative groups has all small colimits.
-/
instance (priority := 1300) hasColimitsOfSize [UnivLE.{u, w}] :
    HasColimitsOfSize.{v, u} (AddCommGrpCat.{w}) where

end AddCommGrpCat

namespace AddCommGrpCat

open QuotientAddGroup

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The categorical cokernel of a morphism in `AddCommGrpCat`
agrees with the usual group-theoretical quotient.
-/
/-
**AddCommGrpCat.cokernelIsoQuotient** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：cokernelIsoQuotient {G H : AddCommGrpCat.{u}} (f : G ⟶ H) : cokernel f ≅ A
ddCommGrpCat.of (H ⧸ AddMonoidHom.range f.hom) where hom
参数：f : G ⟶ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical cokernel of a morphism in `AddCommGrpCat`
agrees with the usual group-theoretical quotient.
-/
noncomputable def cokernelIsoQuotient {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    cokernel f ≅ AddCommGrpCat.of (H ⧸ AddMonoidHom.range f.hom) where
  hom := cokernel.desc f (ofHom (mk' _)) <| by
        ext x
        simp
  inv := ofHom <|
    QuotientAddGroup.lift _ (cokernel.π f).hom <| by
      rintro _ ⟨x, rfl⟩
      exact cokernel.condition_apply f x
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    simp only [coequalizer_as_cokernel, cokernel.π_desc_assoc, Category.comp_id]
    rfl
  inv_hom_id := by
    ext x
    dsimp only [hom_comp, hom_ofHom, hom_zero, AddMonoidHom.coe_comp, coe_mk',
      Function.comp_apply, AddMonoidHom.zero_apply, id_eq, lift_mk, hom_id, AddMonoidHom.coe_id]
    exact QuotientAddGroup.induction_on (α := H) x <| cokernel.π_desc_apply f _ _

end AddCommGrpCat

