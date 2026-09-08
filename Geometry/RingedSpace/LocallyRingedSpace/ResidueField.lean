/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!

# Residue fields of points

Any point `x` of a locally ringed space `X` comes with a natural residue field, namely the residue
field of the stalk at `x`. Moreover, for every open subset of `X` containing `x`, we have a
canonical evaluation map from `Γ(X, U)` to the residue field of `X` at `x`.

## Main definitions

The following are in the `AlgebraicGeometry.LocallyRingedSpace` namespace:

- `residueField`: the residue field of the stalk at `x`.
- `evaluation`: for open subsets `U` of `X` containing `x`, the evaluation map from sections over
  `U` to the residue field at `x`.
- `evaluationMap`: a morphism of locally ringed spaces induces a morphism, i.e. extension, of
  residue fields.

-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u}) {U : Opens X}

/-- The residue field of `X` at a point `x` is the residue field of the stalk of `X`
at `x`. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.residueField** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.LocallyRingedSpace`。
形式化陈述：residueField (x : X) : CommRingCat
参数：x : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)

--- 原说明 ---
The residue field of `X` at a point `x` is the residue field of the stalk of `X`
at `x`.
-/
def residueField (x : X) : CommRingCat :=
  CommRingCat.of <| IsLocalRing.ResidueField (X.presheaf.stalk x)
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : Field (X.residueField x) :=
  inferInstanceAs <| Field (IsLocalRing.ResidueField (X.presheaf.stalk x))

/-- The residue map from the stalk to the residue field. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.residue** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.LocallyRingedSpace`。
形式化陈述：residue (X : LocallyRingedSpace.{u}) (x : X) : X.presheaf.stalk x ⟶ X.resi
dueField x
参数：X : LocallyRingedSpace.{u}；x : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)

--- 原说明 ---
The residue map from the stalk to the residue field.
-/
def residue (X : LocallyRingedSpace.{u}) (x : X) : X.presheaf.stalk x ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))
/-
**AlgebraicGeometry.LocallyRingedSpace.residue_surjective** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：residue_surjective (x : X) : Function.Surjective (X.residue x)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
-/
lemma residue_surjective (x : X) : Function.Surjective (X.residue x) :=
  Ideal.Quotient.mk_surjective
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : Epi (X.residue x) :=
  ConcreteCategory.epi_of_surjective _ (X.residue_surjective x)

/--
If `U` is an open of `X` containing `x`, we have a canonical ring map from the sections
over `U` to the residue field of `x`.

If we interpret sections over `U` as functions of `X` defined on `U`, then this ring map
corresponds to evaluation at `x`.
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.evaluation** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.LocallyRingedSpace`。
形式化陈述：evaluation (x : U) : X.presheaf.obj (op U) ⟶ X.residueField x
参数：x : U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `U` is an open of `X` containing `x`, we have a canonical ring map from the s
ections
over `U` to the residue field of `x`.

If we interpret sections over `U` as functions of `X` defined on `U`, then this 
ring map
corresponds to evaluation at `x`.
-/
def evaluation (x : U) : X.presheaf.obj (op U) ⟶ X.residueField x :=
  X.presheaf.germ U x.1 x.2 ≫ X.residue _

/-- The global evaluation map from `Γ(X, ⊤)` to the residue field at `x`. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The global evaluation map from `Γ(X, ⊤)` to the residue field at `x`.
-/
def Γevaluation (x : X) : X.presheaf.obj (op ⊤) ⟶ X.residueField x :=
  X.evaluation ⟨x, show x ∈ ⊤ from trivial⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen**
 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：evaluation_eq_zero_iff_notMem_basicOpen (x : U) (f : X.presheaf.obj (op U)
) : X.evaluation x f = 0 ↔ x.val ∉ X.toRingedSpace.basicOpen f
参数：x : U；f : X.presheaf.obj (op U)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.RingedSpace.mem_basicOpen`：mem_basicOpen {U : Opens X}
 (f : X.presheaf.obj (op U)) (x : X) (hx : x in U) : x in X.basicOpen f ↔ IsUnit
 (X.presheaf.germ U x hx f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用引理 `IsLocalRing.residue_ne_zero_iff_isUnit`：residue_ne_zero_iff_isUnit (x : 
R) : residue R x != 0 ↔ IsUnit x
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
-/
lemma evaluation_eq_zero_iff_notMem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f = 0 ↔ x.val ∉ X.toRingedSpace.basicOpen f := by
  rw [X.toRingedSpace.mem_basicOpen f x.1 x.2, ← not_iff_not, not_not]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _)
/-
**AlgebraicGeometry.LocallyRingedSpace.evaluation_ne_zero_iff_mem_basicOpen** 是 
Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：evaluation_ne_zero_iff_mem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
 X.evaluation x f != 0 ↔ x.val in X.toRingedSpace.basicOpen f
参数：x : U；f : X.presheaf.obj (op U)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma evaluation_ne_zero_iff_mem_basicOpen (x : U) (f : X.presheaf.obj (op U)) :
    X.evaluation x f ≠ 0 ↔ x.val ∈ X.toRingedSpace.basicOpen f := by
  simp
/-
**AlgebraicGeometry.LocallyRingedSpace.basicOpen_eq_bot_iff_forall_evaluation_eq
_zero** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj (op U))
 : X.toRingedSpace.basicOpen f = ⊥ ↔ forall (x : U), X.evaluation x f = 0
参数：f : X.presheaf.obj (op U)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `AlgebraicGeometry.RingedSpace.basicOpen_le`：basicOpen_le {U : Opens X} (
f : X.presheaf.obj (op U)) : X.basicOpen f <= U
-/
lemma basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj (op U)) :
    X.toRingedSpace.basicOpen f = ⊥ ↔ ∀ (x : U), X.evaluation x f = 0 := by
  simp only [evaluation_eq_zero_iff_notMem_basicOpen, Subtype.forall]
  exact ⟨fun h ↦ h ▸ fun a _ hc ↦ hc,
    fun h ↦ eq_bot_iff.mpr <| fun a ha ↦ h a (X.toRingedSpace.basicOpen_le f ha) ha⟩

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Γevaluation_eq_zero_iff_notMem_basicOpen (x : X) (f : X.presheaf.obj (op ⊤)) :
    X.Γevaluation x f = 0 ↔ x ∉ X.toRingedSpace.basicOpen f :=
  evaluation_eq_zero_iff_notMem_basicOpen X ⟨x, show x ∈ ⊤ by trivial⟩ f
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Γevaluation_ne_zero_iff_mem_basicOpen (x : X) (f : X.presheaf.obj (op ⊤)) :
    X.Γevaluation x f ≠ 0 ↔ x ∈ X.toRingedSpace.basicOpen f :=
  evaluation_ne_zero_iff_mem_basicOpen X ⟨x, show x ∈ ⊤ by trivial⟩ f

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)

/-- If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obtain
a morphism of residue fields in the other direction. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.residueFieldMap** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：residueFieldMap (x : X) : Y.residueField (f.base x) ⟶ X.residueField x
参数：x : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.isLocalHomValStalkMap`：isLocalHomVa
lStalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X) : IsLocalHom (f.s
talkMap x).hom

--- 原说明 ---
If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obt
ain
a morphism of residue fields in the other direction.
-/
def residueFieldMap (x : X) : Y.residueField (f.base x) ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.ResidueField.map (f.stalkMap x).hom)

@[reassoc]
/-
**AlgebraicGeometry.LocallyRingedSpace.residue_comp_residueFieldMap_eq_stalkMap_
comp_residue** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：residue_comp_residueFieldMap_eq_stalkMap_comp_residue (x : X) : Y.residue 
_ ≫ residueFieldMap f x = f.stalkMap x ≫ X.residue _
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.isLocalHomValStalkMap`：isLocalHomVa
lStalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X) : IsLocalHom (f.s
talkMap x).hom
-/
lemma residue_comp_residueFieldMap_eq_stalkMap_comp_residue (x : X) :
    Y.residue _ ≫ residueFieldMap f x = f.stalkMap x ≫ X.residue _ := by
  simp [residueFieldMap]
  rfl

@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.residueFieldMap_id** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：residueFieldMap_id (x : X) : residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x
)
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.isLocalHomValStalkMap`：isLocalHomVa
lStalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X) : IsLocalHom (f.s
talkMap x).hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_id`：stalkMap_id (X : Local
lyRingedSpace.{u}) (x : X) : (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalRing.ResidueField.map.congr_simp`：∀ {R : Type u_1} {S : Type u_2}
 [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst_3 : 
IsLocalRing S] (f f_1 : R →+*…
· 使用定理 `IsLocalRing.ResidueField.map_id`：map_id : IsLocalRing.ResidueField.map (
RingHom.id R) = RingHom.id (IsLocalRing.ResidueField R)
-/
lemma residueFieldMap_id (x : X) :
    residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) := by
  ext : 1
  simp only [residueFieldMap, stalkMap_id]
  apply IsLocalRing.ResidueField.map_id

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.LocallyRingedSpace.residueFieldMap_comp** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：residueFieldMap_comp {Z : LocallyRingedSpace.{u}} (g : Y ⟶ Z) (x : X) : re
sidueFieldMap (f ≫ g) x = residueFieldMap g (f.base x) ≫ residueFieldMap f x
参数：g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.isLocalHomValStalkMap`：isLocalHomVa
lStalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X) : IsLocalHom (f.s
talkMap x).hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp`：stalkMap_comp (x : X
) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f.base x) ≫ f.stalkMap x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalRing.ResidueField.map.congr_simp`：∀ {R : Type u_1} {S : Type u_2}
 [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst_3 : 
IsLocalRing S] (f f_1 : R →+*…
· 使用定理 `IsLocalRing.ResidueField.map_comp`：map_comp (f : T ->+* R) (g : R ->+* S
) [IsLocalHom f] [IsLocalHom g] : IsLocalRing.ResidueField.map (g.comp f) = (IsL
ocalRing.ResidueField.m…
-/
lemma residueFieldMap_comp {Z : LocallyRingedSpace.{u}} (g : Y ⟶ Z) (x : X) :
    residueFieldMap (f ≫ g) x = residueFieldMap g (f.base x) ≫ residueFieldMap f x := by
  ext : 1
  simp only [residueFieldMap, stalkMap_comp]
  apply IsLocalRing.ResidueField.map_comp (Hom.stalkMap g (f.base x)).hom (Hom.stalkMap f x).hom

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.LocallyRingedSpace.evaluation_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：evaluation_naturality {V : Opens Y} (x : (Opens.map f.base).obj V) : Y.eva
luation ⟨f.base x, x.property⟩ ≫ residueFieldMap f x.val = f.c.app (op V) ≫ X.ev
aluation x
参数：x : (Opens.map f.base).obj V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.isLocalHomValStalkMap`：isLocalHomVa
lStalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X) : IsLocalHom (f.s
talkMap x).hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CommRingCat.comp_apply`：comp_apply {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T) (r : R) : (f ≫ g) r = g (f r)
· 使用定理 `IsLocalRing.ResidueField.map_residue`：map_residue (f : R ->+* S) [IsLoca
lHom f] (r : R) : ResidueField.map f (residue R r) = residue S (f r)
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ_apply`：stalkMap_germ_
apply (U : Opens Y) (x : X) (hx : f.base x in U) (y) : f.stalkMap x (Y.presheaf.
germ U (f.base x) hx y) = X.presheaf.germ ((Op…
-/
lemma evaluation_naturality {V : Opens Y} (x : (Opens.map f.base).obj V) :
    Y.evaluation ⟨f.base x, x.property⟩ ≫ residueFieldMap f x.val =
      f.c.app (op V) ≫ X.evaluation x := by
  dsimp only [LocallyRingedSpace.evaluation,
    LocallyRingedSpace.residueFieldMap]
  rw [Category.assoc]
  ext a
  simp only [CommRingCat.comp_apply]
  erw [IsLocalRing.ResidueField.map_residue]
  rw [LocallyRingedSpace.stalkMap_germ_apply]
  rfl
/-
**AlgebraicGeometry.LocallyRingedSpace.evaluation_naturality_apply** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace`。
形式化陈述：evaluation_naturality_apply {V : Opens Y} (x : (Opens.map f.base).obj V) (
a : Y.presheaf.obj (op V)) : residueFieldMap f x.val (Y.evaluation ⟨f.base x, x.
property⟩ a) = X.evaluation x (f.c.app (op V) a)
参数：x : (Opens.map f.base).obj V；a : Y.presheaf.obj (op V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.evaluation_naturality`：evaluation_n
aturality {V : Opens Y} (x : (Opens.map f.base).obj V) : Y.evaluation ⟨f.base x,
 x.property⟩ ≫ residueFieldMap f x.val = f.c.app…
-/
lemma evaluation_naturality_apply {V : Opens Y} (x : (Opens.map f.base).obj V)
    (a : Y.presheaf.obj (op V)) :
    residueFieldMap f x.val (Y.evaluation ⟨f.base x, x.property⟩ a) =
      X.evaluation x (f.c.app (op V) a) := by
  simpa using! congrFun (congrArg (DFunLike.coe ∘ CommRingCat.Hom.hom) <|
    evaluation_naturality f x) a

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f.base x) ≫ residueFieldMap f x =
      f.c.app (op ⊤) ≫ X.Γevaluation x :=
  evaluation_naturality f ⟨x, by simp only [Opens.map_top]; trivial⟩
/-
**AlgebraicGeometry.LocallyRingedSpace.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.LocallyRingedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Γevaluation_naturality_apply (x : X) (a : Y.presheaf.obj (op ⊤)) :
    residueFieldMap f x (Y.Γevaluation (f.base x) a) =
      X.Γevaluation x (f.c.app (op ⊤) a) :=
  evaluation_naturality_apply f ⟨x, by simp only [Opens.map_top]; trivial⟩ a

end LocallyRingedSpace

end AlgebraicGeometry

