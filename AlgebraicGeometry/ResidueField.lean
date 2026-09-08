/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField

/-!

# Residue fields of points

## Main definitions

The following are in the `AlgebraicGeometry.Scheme` namespace:

- `AlgebraicGeometry.Scheme.residueField`: The residue field of the stalk at `x`.
- `AlgebraicGeometry.Scheme.evaluation`: For open subsets `U` of `X` containing `x`,
  the evaluation map from sections over `U` to the residue field at `x`.
- `AlgebraicGeometry.Scheme.Hom.residueFieldMap`: A morphism of schemes induce a homomorphism of
  residue fields.
- `AlgebraicGeometry.Scheme.fromSpecResidueField`: The canonical map `Spec κ(x) ⟶ X`.
- `AlgebraicGeometry.Scheme.SpecToEquivOfField`: morphisms `Spec K ⟶ X` for a field `K` correspond
  to pairs of `x : X` with embedding `κ(x) ⟶ K`.


-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite IsLocalRing

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {U : X.Opens}

/-- The residue field of `X` at a point `x` is the residue field of the stalk of `X`
at `x`. -/
/-
**AlgebraicGeometry.Scheme.residueField** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：residueField (x : X) : CommRingCat
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The residue field of `X` at a point `x` is the residue field of the stalk of `X`
at `x`.
-/
def residueField (x : X) : CommRingCat :=
  CommRingCat.of <| IsLocalRing.ResidueField (X.presheaf.stalk x)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : Field (X.residueField x) :=
  inferInstanceAs <| Field (IsLocalRing.ResidueField (X.presheaf.stalk x))
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : Unique (Spec (X.residueField x)) := inferInstanceAs (Unique (Spec <| .of _))

/-- The residue map from the stalk to the residue field. -/
/-
**AlgebraicGeometry.Scheme.residue** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.
Scheme`。
形式化陈述：residue (X : Scheme.{u}) (x) : X.presheaf.stalk x ⟶ X.residueField x
参数：X : Scheme.{u}；x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The residue map from the stalk to the residue field.
-/
def residue (X : Scheme.{u}) (x) : X.presheaf.stalk x ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

/-- See `AlgebraicGeometry.IsClosedImmersion.SpecMap_residue` for the stronger result that
`Spec.map (X.residue x)` is a closed immersion. -/
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `AlgebraicGeometry.IsClosedImmersion.SpecMap_residue` for the stronger resul
t that
`Spec.map (X.residue x)` is a closed immersion.
-/
instance {X : Scheme.{u}} (x) : IsPreimmersion (Spec.map (X.residue x)) :=
  IsPreimmersion.mk_SpecMap
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isEmbedding
    (RingHom.surjectiveOnStalks_of_surjective (Ideal.Quotient.mk_surjective))

@[simp]
/-
**AlgebraicGeometry.Scheme.SpecMap_residue_apply** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：SpecMap_residue_apply {X : Scheme.{u}} (x : X) (s : Spec (X.residueField x
)) : Spec.map (X.residue x) s = closedPoint (X.presheaf.stalk x)
参数：x : X；s : Spec (X.residueField x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.PrimeSpectrum.comap_residue`：∀ (T : Type u) [inst : CommRing
 T] [inst_1 : IsLocalRing T] (x : PrimeSpectrum (IsLocalRing.ResidueField T)),  
 PrimeSpectrum.comap (IsLocal…
-/
lemma SpecMap_residue_apply {X : Scheme.{u}} (x : X) (s : Spec (X.residueField x)) :
    Spec.map (X.residue x) s = closedPoint (X.presheaf.stalk x) :=
  IsLocalRing.PrimeSpectrum.comap_residue _ s
/-
**AlgebraicGeometry.Scheme.residue_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：residue_surjective (X : Scheme.{u}) (x) : Function.Surjective (X.residue x
)
参数：X : Scheme.{u}；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
-/
lemma residue_surjective (X : Scheme.{u}) (x) : Function.Surjective (X.residue x) :=
  Ideal.Quotient.mk_surjective
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Scheme.{u}) (x) : Epi (X.residue x) :=
  ConcreteCategory.epi_of_surjective _ (X.residue_surjective x)

/-- If `K` is a field and `f : 𝒪_{X, x} ⟶ K` is a ring map, then this is the induced
map `κ(x) ⟶ K`. -/
/-
**AlgebraicGeometry.Scheme.descResidueField** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：descResidueField {K : Type u} [Field K] {X : Scheme.{u}} {x : X} (f : X.pr
esheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] : X.residueField x ⟶ .of K
参数：f : X.presheaf.stalk x ⟶ .of K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K` is a field and `f : 𝒪_{X, x} ⟶ K` is a ring map, then this is the induced
map `κ(x) ⟶ K`.
-/
def descResidueField {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    X.residueField x ⟶ .of K :=
  CommRingCat.ofHom (IsLocalRing.ResidueField.lift (S := K) f.hom)

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.residue_descResidueField** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry.Scheme`。
形式化陈述：residue_descResidueField {K : Type u} [Field K] {X : Scheme.{u}} {x} (f : 
X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] : X.residue x ≫ X.descResidueFiel
d f = f
参数：f : X.presheaf.stalk x ⟶ .of K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
lemma residue_descResidueField {K : Type u} [Field K] {X : Scheme.{u}} {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    X.residue x ≫ X.descResidueField f = f :=
  CommRingCat.hom_ext <| RingHom.ext fun _ ↦ rfl

/--
If `U` is an open of `X` containing `x`, we have a canonical ring map from the sections
over `U` to the residue field of `x`.

If we interpret sections over `U` as functions of `X` defined on `U`, then this ring map
corresponds to evaluation at `x`.
-/
/-
**AlgebraicGeometry.Scheme.evaluation** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
形式化陈述：evaluation (U : X.Opens) (x : X) (hx : x in U) : Γ(X, U) ⟶ X.residueField 
x
参数：U : X.Opens；x : X；hx : x in U。
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
def evaluation (U : X.Opens) (x : X) (hx : x ∈ U) : Γ(X, U) ⟶ X.residueField x :=
  X.presheaf.germ U x hx ≫ X.residue _

@[reassoc]
/-
**AlgebraicGeometry.Scheme.germ_residue** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：germ_residue (x hx) : X.presheaf.germ U x hx ≫ X.residue x = X.evaluation 
U x hx
参数：x hx。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma germ_residue (x hx) : X.presheaf.germ U x hx ≫ X.residue x = X.evaluation U x hx := rfl

/-- The global evaluation map from `Γ(X, ⊤)` to the residue field at `x`. -/
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeometry.Schem
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The global evaluation map from `Γ(X, ⊤)` to the residue field at `x`.
-/
abbrev Γevaluation (x : X) : Γ(X, ⊤) ⟶ X.residueField x :=
  X.evaluation ⊤ x trivial

@[simp]
/-
**AlgebraicGeometry.Scheme.evaluation_eq_zero_iff_notMem_basicOpen** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：evaluation_eq_zero_iff_notMem_basicOpen (x : X) (hx : x in U) (f : Γ(X, U)
) : X.evaluation U x hx f = 0 ↔ x ∉ X.basicOpen f
参数：x : X；hx : x in U；f : Γ(X, U)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.evaluation_eq_zero_iff_notMem_basic
Open`：evaluation_eq_zero_iff_notMem_basicOpen (x : U) (f : X.presheaf.obj (op U)
) : X.evaluation x f = 0 ↔ x.val ∉ X.toRingedSpace.basicOpen f
-/
lemma evaluation_eq_zero_iff_notMem_basicOpen (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f = 0 ↔ x ∉ X.basicOpen f :=
  X.toLocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen ⟨x, hx⟩ f
/-
**AlgebraicGeometry.Scheme.evaluation_ne_zero_iff_mem_basicOpen** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：evaluation_ne_zero_iff_mem_basicOpen (x : X) (hx : x in U) (f : Γ(X, U)) :
 X.evaluation U x hx f != 0 ↔ x in X.basicOpen f
参数：x : X；hx : x in U；f : Γ(X, U)。
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
lemma evaluation_ne_zero_iff_mem_basicOpen (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f ≠ 0 ↔ x ∈ X.basicOpen f := by
  simp
/-
**AlgebraicGeometry.Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero** 是 Ma
thlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj (op U))
 : X.basicOpen f = ⊥ ↔ forall (x : U), X.evaluation U x x.property f = 0
参数：f : X.presheaf.obj (op U)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.basicOpen_eq_bot_iff_forall_evaluat
ion_eq_zero`：basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj 
(op U)) : X.toRingedSpace.basicOpen f = ⊥ ↔ forall (x : U), X.evaluation …
-/
lemma basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj (op U)) :
    X.basicOpen f = ⊥ ↔ ∀ (x : U), X.evaluation U x x.property f = 0 :=
  X.toLocallyRingedSpace.basicOpen_eq_bot_iff_forall_evaluation_eq_zero f

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obtain
a morphism of residue fields in the other direction. -/
/-
**AlgebraicGeometry.Scheme.Hom.residueFieldMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : X ⟶ Y) → (x : ↥X) → Y.residueField
 (f x) ⟶ X.residueField x
参数：f : X ⟶ Y；x : ↥X；f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsLocalHomCarrierStalkCommRingCatPreshe
afCoeContinuousMapCarrierCarrierHomTopCatBaseRingHomHomStalkMap`：∀ {X Y : Algebr
aicGeometry.Scheme} (f : X ⟶ Y) (x : ↥X),   IsLocalHom (CommRingCat.Hom.hom (Alg
ebraicGeometry.Scheme.Hom.stalkMap f x))

--- 原说明 ---
If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obt
ain
a morphism of residue fields in the other direction.
-/
def Hom.residueFieldMap (f : X ⟶ Y) (x : X) :
    Y.residueField (f x) ⟶ X.residueField x :=
  CommRingCat.ofHom <| IsLocalRing.ResidueField.map (f.stalkMap x).hom

@[reassoc]
/-
**AlgebraicGeometry.Scheme.residue_residueFieldMap** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme`。
形式化陈述：residue_residueFieldMap (x : X) : Y.residue (f x) ≫ f.residueFieldMap x = 
f.stalkMap x ≫ X.residue x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsLocalHomCarrierStalkCommRingCatPreshe
afCoeContinuousMapCarrierCarrierHomTopCatBaseRingHomHomStalkMap`：∀ {X Y : Algebr
aicGeometry.Scheme} (f : X ⟶ Y) (x : ↥X),   IsLocalHom (CommRingCat.Hom.hom (Alg
ebraicGeometry.Scheme.Hom.stalkMap f x))
-/
lemma residue_residueFieldMap (x : X) :
    Y.residue (f x) ≫ f.residueFieldMap x = f.stalkMap x ≫ X.residue x := by
  simp [Hom.residueFieldMap]
  rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.residueFieldMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：residueFieldMap_id (x : X) : Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueFie
ld x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.residueFieldMap_id`：residueFieldMap
_id (x : X) : residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x)
-/
lemma residueFieldMap_id (x : X) :
    Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) :=
  LocallyRingedSpace.residueFieldMap_id _

@[simp]
/-
**AlgebraicGeometry.Scheme.residueFieldMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：residueFieldMap_comp {Z : Scheme.{u}} (g : Y ⟶ Z) (x : X) : (f ≫ g).residu
eFieldMap x = g.residueFieldMap (f x) ≫ f.residueFieldMap x
参数：g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.residueFieldMap_comp`：residueFieldM
ap_comp {Z : LocallyRingedSpace.{u}} (g : Y ⟶ Z) (x : X) : residueFieldMap (f ≫ 
g) x = residueFieldMap g (f.base x) ≫ residueFi…
-/
lemma residueFieldMap_comp {Z : Scheme.{u}} (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueFieldMap x = g.residueFieldMap (f x) ≫ f.residueFieldMap x :=
  LocallyRingedSpace.residueFieldMap_comp _ _ _

/--
Degree of `f` at a point `x` is defined to be the degree of the associated field extension
from `κ(f x)` to `κ(x)`. We return a default value of zero when this degree is infinite.
-/
/-
**AlgebraicGeometry.Scheme.Hom.residueDegree** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → ↥X → ℕ
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Degree of `f` at a point `x` is defined to be the degree of the associated field
 extension
from `κ(f x)` to `κ(x)`. We return a default value of zero when this degree is i
nfinite.
-/
def Hom.residueDegree (f : X ⟶ Y) (x : X) : ℕ :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (f x)) (X.residueField x)

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.residueDegree_id** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (x : ↥X),   AlgebraicGeometry.Scheme.Hom.
residueDegree (CategoryTheory.CategoryStruct.id X) x = 1
参数：x : ↥X；CategoryTheory.CategoryStruct.id X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.residueFieldMap_id`：residueFieldMap_id (x : X) 
: Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x)
· 使用定理 `CommSemiring.finrank_self`：CommSemiring.finrank_self (R) [CommSemiring R
] : Module.finrank R R = 1
-/
lemma Hom.residueDegree_id (x : X) : (𝟙 _ : X ⟶ X).residueDegree x = 1 := by
  dsimp [residueDegree]
  rw [residueFieldMap_id]
  exact CommSemiring.finrank_self _

@[reassoc]
/-
**AlgebraicGeometry.Scheme.evaluation_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：evaluation_naturality {V : Opens Y} (x : X) (hx : f x in V) : Y.evaluation
 V (f x) hx ≫ f.residueFieldMap x = f.app V ≫ X.evaluation (f ⁻¹ᵁ V) x hx
参数：x : X；hx : f x in V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.evaluation_naturality`：evaluation_n
aturality {V : Opens Y} (x : (Opens.map f.base).obj V) : Y.evaluation ⟨f.base x,
 x.property⟩ ≫ residueFieldMap f x.val = f.c.app…
-/
lemma evaluation_naturality {V : Opens Y} (x : X) (hx : f x ∈ V) :
    Y.evaluation V (f x) hx ≫ f.residueFieldMap x =
      f.app V ≫ X.evaluation (f ⁻¹ᵁ V) x hx :=
  LocallyRingedSpace.evaluation_naturality f.1 ⟨x, hx⟩
/-
**AlgebraicGeometry.Scheme.evaluation_naturality_apply** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme`。
形式化陈述：evaluation_naturality_apply {V : Opens Y} (x : X) (hx : f x in V) (s) : f.
residueFieldMap x (Y.evaluation V (f x) hx s) = X.evaluation (f ⁻¹ᵁ V) x hx (f.a
pp V s)
参数：x : X；hx : f x in V；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.evaluation_naturality_apply`：evalua
tion_naturality_apply {V : Opens Y} (x : (Opens.map f.base).obj V) (a : Y.preshe
af.obj (op V)) : residueFieldMap f x.val (Y.evaluation…
-/
lemma evaluation_naturality_apply {V : Opens Y} (x : X) (hx : f x ∈ V) (s) :
    f.residueFieldMap x (Y.evaluation V (f x) hx s) =
      X.evaluation (f ⁻¹ᵁ V) x hx (f.app V s) :=
  LocallyRingedSpace.evaluation_naturality_apply f.1 ⟨x, hx⟩ s

@[reassoc]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f x) ≫ f.residueFieldMap x = f.appTop ≫ X.Γevaluation x :=
  LocallyRingedSpace.Γevaluation_naturality f.toLRSHom x
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Γevaluation_naturality_apply (x : X) (a : Y.presheaf.obj (op ⊤)) :
    f.residueFieldMap x (Y.Γevaluation (f x) a) = X.Γevaluation x (f.appTop a) :=
  LocallyRingedSpace.Γevaluation_naturality_apply f.toLRSHom x a
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsOpenImmersion f] (x) : IsIso (f.residueFieldMap x) :=
  (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

section congr

-- replace this def if hard to work with
/-- The isomorphism between residue fields of equal points. -/
/-
**AlgebraicGeometry.Scheme.residueFieldCongr** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：residueFieldCongr {x y : X} (h : x = y) : X.residueField x ≅ X.residueFiel
d y
参数：h : x = y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between residue fields of equal points.
-/
def residueFieldCongr {x y : X} (h : x = y) :
    X.residueField x ≅ X.residueField y :=
  eqToIso (by subst h; rfl)

@[simp]
/-
**AlgebraicGeometry.Scheme.residueFieldCongr_refl** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme`。
形式化陈述：residueFieldCongr_refl {x : X} : X.residueFieldCongr (refl x) = Iso.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
-/
lemma residueFieldCongr_refl {x : X} :
    X.residueFieldCongr (refl x) = Iso.refl _ := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.residueFieldCongr_symm** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme`。
形式化陈述：residueFieldCongr_symm {x y : X} (e : x = y) : (X.residueFieldCongr e).sym
m = X.residueFieldCongr e.symm
参数：e : x = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma residueFieldCongr_symm {x y : X} (e : x = y) :
    (X.residueFieldCongr e).symm = X.residueFieldCongr e.symm := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.residueFieldCongr_inv** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：residueFieldCongr_inv {x y : X} (e : x = y) : (X.residueFieldCongr e).inv 
= (X.residueFieldCongr e.symm).hom
参数：e : x = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma residueFieldCongr_inv {x y : X} (e : x = y) :
    (X.residueFieldCongr e).inv = (X.residueFieldCongr e.symm).hom := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.residueFieldCongr_trans** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme`。
形式化陈述：residueFieldCongr_trans {x y z : X} (e : x = y) (e' : y = z) : X.residueFi
eldCongr e ≪≫ X.residueFieldCongr e' = X.residueFieldCongr (e.trans e')
参数：e : x = y；e' : y = z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma residueFieldCongr_trans {x y z : X} (e : x = y) (e' : y = z) :
    X.residueFieldCongr e ≪≫ X.residueFieldCongr e' = X.residueFieldCongr (e.trans e') := by
  subst e e'
  rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.residueFieldCongr_trans_hom** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme`。
形式化陈述：residueFieldCongr_trans_hom (X : Scheme) {x y z : X} (e : x = y) (e' : y =
 z) : (X.residueFieldCongr e).hom ≫ (X.residueFieldCongr e').hom = (X.residueFie
ldCongr (e.trans e')).hom
参数：X : Scheme；e : x = y；e' : y = z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma residueFieldCongr_trans_hom (X : Scheme) {x y z : X} (e : x = y) (e' : y = z) :
    (X.residueFieldCongr e).hom ≫ (X.residueFieldCongr e').hom =
      (X.residueFieldCongr (e.trans e')).hom := by
  subst e e'
  rfl

@[reassoc]
/-
**AlgebraicGeometry.Scheme.residue_residueFieldCongr** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme`。
形式化陈述：residue_residueFieldCongr (X : Scheme) {x y : X} (h : x = y) : X.residue x
 ≫ (X.residueFieldCongr h).hom = (X.presheaf.stalkCongr (.of_eq h)).hom ≫ X.resi
due y
参数：X : Scheme；h : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopCat.Presheaf.stalkCongr_hom`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `TopCat.Presheaf.stalkSpecializes_refl`：stalkSpecializes_refl (F : X.Pres
heaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma residue_residueFieldCongr (X : Scheme) {x y : X} (h : x = y) :
    X.residue x ≫ (X.residueFieldCongr h).hom =
      (X.presheaf.stalkCongr (.of_eq h)).hom ≫ X.residue y := by
  subst h
  simp
/-
**AlgebraicGeometry.Scheme.Hom.residueFieldMap_congr** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f g : X ⟶ Y} (e : f = g) (x : ↥X),   A
lgebraicGeometry.Scheme.Hom.residueFieldMap f x =     CategoryTheory.CategoryStr
uct.comp (AlgebraicGeometry.Scheme.residueFieldCongr ⋯).hom       (AlgebraicGeom
etry.Scheme.Hom.residueFieldMap g x)
参数：e : f = g；x : ↥X；AlgebraicGeometry.Scheme.residueFieldCongr ⋯；AlgebraicGeomet
ry.Scheme.Hom.residueFieldMap g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.residueFieldMap_congr {f g : X ⟶ Y} (e : f = g) (x : X) :
    f.residueFieldMap x = (Y.residueFieldCongr (by subst e; rfl)).hom ≫ g.residueFieldMap x := by
  subst e; simp

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.residueFieldMap_congr'** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {x₁ x₂ : ↥X} (e : x₁ = x₂),
   CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Scheme.Hom.residueField
Map f x₁)       (AlgebraicGeometry.Scheme.residueFieldCongr e).hom =     Categor
yTheory.CategoryStruct.comp (AlgebraicGeometry.Scheme.residueFieldCongr ⋯).hom  
     (AlgebraicGeometry.Scheme.Hom.residueFieldMap f x₂)
参数：e : x₁ = x₂；AlgebraicGeometry.Scheme.Hom.residueFieldMap f x₁；AlgebraicGeomet
ry.Scheme.residueFieldCongr e；AlgebraicGeometry.Scheme.residueFieldCongr ⋯；Algeb
raicGeometry.Scheme.Hom.residueFieldMap f x₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.residueFieldMap_congr' {f : X ⟶ Y} {x₁ x₂ : X} (e : x₁ = x₂) :
    f.residueFieldMap x₁ ≫ (X.residueFieldCongr e).hom =
      (Y.residueFieldCongr (congrArg f e)).hom ≫ f.residueFieldMap x₂ := by
  subst e
  simp

end congr

section fromResidueField

/-- The canonical map `Spec κ(x) ⟶ X`. -/
/-
**AlgebraicGeometry.Scheme.fromSpecResidueField** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：fromSpecResidueField (X : Scheme) (x : X) : Spec (X.residueField x) ⟶ X
参数：X : Scheme；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `Spec κ(x) ⟶ X`.
-/
def fromSpecResidueField (X : Scheme) (x : X) :
    Spec (X.residueField x) ⟶ X :=
  Spec.map (X.residue x) ≫ X.fromSpecStalk x
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} (x : X) : IsPreimmersion (X.fromSpecResidueField x) := by
  dsimp only [Scheme.fromSpecResidueField]
  rw [IsPreimmersion.comp_iff]
  infer_instance

@[simps] noncomputable
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : (Spec (X.residueField x)).Over X := ⟨X.fromSpecResidueField x⟩

noncomputable
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : (Spec (X.residueField x)).CanonicallyOver X where

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.residueFieldCongr_fromSpecResidueField** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：residueFieldCongr_fromSpecResidueField {x y : X} (h : x = y) : Spec.map (X
.residueFieldCongr h).hom ≫ X.fromSpecResidueField _ = X.fromSpecResidueField _
参数：h : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma residueFieldCongr_fromSpecResidueField {x y : X} (h : x = y) :
    Spec.map (X.residueFieldCongr h).hom ≫ X.fromSpecResidueField _ =
      X.fromSpecResidueField _ := by
  subst h; simp
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {x y : X} (h : x = y) : (Spec.map (X.residueFieldCongr h).hom).IsOver X where

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (x : ↥X),   CategoryTheory.
CategoryStruct.comp (AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.Hom.re
sidueFieldMap f x))       (Y.fromSpecResidueField (f x)) =     CategoryTheory.Ca
tegoryStruct.comp (X.fromSpecResidueField x) f
参数：f : X ⟶ Y；x : ↥X；AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.Hom.res
idueFieldMap f x)；Y.fromSpecResidueField (f x)；X.fromSpecResidueField x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_stalkMap_fromSpecStalk`：SpecMap_stalkMa
p_fromSpecStalk {x} : Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ = X.fromSpecSt
alk x ≫ f
· 使用定理 `AlgebraicGeometry.Spec.map_comp_assoc`：∀ {R S T : CommRingCat} (f : R ⟶ 
S) (g : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.Category…
-/
lemma Hom.SpecMap_residueFieldMap_fromSpecResidueField (x : X) :
    Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField _ =
      X.fromSpecResidueField x ≫ f := by
  dsimp only [fromSpecResidueField]
  rw [Category.assoc, ← SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc]
  rfl
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Over Y] (x : X) : Spec.map ((X ↘ Y).residueFieldMap x) |>.IsOver Y where

@[simp]
/-
**AlgebraicGeometry.Scheme.fromSpecResidueField_apply** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：fromSpecResidueField_apply (x : X.carrier) (s : Spec (X.residueField x)) :
 X.fromSpecResidueField x s = x
参数：x : X.carrier；s : Spec (X.residueField x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_residue_apply`：SpecMap_residue_apply {X
 : Scheme.{u}} (x : X) (s : Spec (X.residueField x)) : Spec.map (X.residue x) s 
= closedPoint (X.presheaf.stalk x)
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint`：fromSpecStalk_closed
Point {x : X} : X.fromSpecStalk x (closedPoint (X.presheaf.stalk x)) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSpecResidueField_apply (x : X.carrier) (s : Spec (X.residueField x)) :
    X.fromSpecResidueField x s = x := by
  simp [fromSpecResidueField]
/-
**AlgebraicGeometry.Scheme.range_fromSpecResidueField** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：range_fromSpecResidueField (x : X.carrier) : Set.range (X.fromSpecResidueF
ield x) = {x}
参数：x : X.carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.instNonemptyCarrierCarrierCommRingCatSpecOfNontrivialC
arrier`：∀ {A : CommRingCat} [Nontrivial ↑A], Nonempty ↥(AlgebraicGeometry.Spec A
)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma range_fromSpecResidueField (x : X.carrier) :
    Set.range (X.fromSpecResidueField x) = {x} := by
  simp
/-
**AlgebraicGeometry.Scheme.descResidueField_fromSpecResidueField** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：descResidueField_fromSpecResidueField {K : Type*} [Field K] (X : Scheme) {
x} (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] : Spec.map (X.descResidue
Field f) ≫ X.fromSpecResidueField x = Spec.map f ≫ X.fromSpecStalk x
参数：X : Scheme；f : X.presheaf.stalk x ⟶ .of K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.residue_descResidueField`：residue_descResidueFi
eld {K : Type u} [Field K] {X : Scheme.{u}} {x} (f : X.presheaf.stalk x ⟶ .of K)
 [IsLocalHom f.hom] : X.residue x ≫ X.d…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma descResidueField_fromSpecResidueField {K : Type*} [Field K] (X : Scheme) {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    Spec.map (X.descResidueField f) ≫
      X.fromSpecResidueField x = Spec.map f ≫ X.fromSpecStalk x := by
  simp [fromSpecResidueField, ← Spec.map_comp_assoc]
/-
**AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueFi
eld** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：descResidueField_stalkClosedPointTo_fromSpecResidueField (K : Type u) [Fie
ld K] (X : Scheme.{u}) (f : Spec (.of K) ⟶ X) : Spec.map (descResidueField (Sche
me.stalkClosedPointTo f)) ≫ X.fromSpecResidueField (f (closedPoint K)) = f
参数：K : Type u；X : Scheme.{u}；f : Spec (.of K) ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.descResidueField_fromSpecResidueField`：descResi
dueField_fromSpecResidueField {K : Type*} [Field K] (X : Scheme) {x} (f : X.pres
heaf.stalk x ⟶ .of K) [IsLocalHom f.hom] : Spec.map …
· 使用引理 `AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk`：Spec_sta
lkClosedPointTo_fromSpecStalk : Spec.map (stalkClosedPointTo f) ≫ X.fromSpecStal
k _ = f
-/
lemma descResidueField_stalkClosedPointTo_fromSpecResidueField
    (K : Type u) [Field K] (X : Scheme.{u}) (f : Spec (.of K) ⟶ X) :
    Spec.map (descResidueField (Scheme.stalkClosedPointTo f)) ≫
      X.fromSpecResidueField (f (closedPoint K)) = f := by
  rw [X.descResidueField_fromSpecResidueField, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

end fromResidueField

section Spec

variable (R : CommRingCat) (x : Spec R)

set_option backward.isDefEq.respectTransparency.types false in
/-- The residue fields of `Spec R` are isomorphic to `Ideal.ResidueField`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Spec.residueFieldIso** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme.Spec`。
形式化陈述：(R : CommRingCat) →   (x : ↥(AlgebraicGeometry.Spec R)) → (AlgebraicGeomet
ry.Spec R).residueField x ≅ CommRingCat.of x.asIdeal.ResidueField
参数：AlgebraicGeometry.Spec R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Spec.residueFieldIso :
    (Spec R).residueField x ≅ .of x.asIdeal.ResidueField :=
  (IsLocalRing.ResidueField.mapEquiv
    (Spec.stalkIso R x).commRingCatIsoToRingEquiv).toCommRingCatIso

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Spec.algebraMap_residueFieldIso_inv** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.Scheme.Spec`。
形式化陈述：∀ (R : CommRingCat) (x : ↥(AlgebraicGeometry.Spec R)),   CategoryTheory.Ca
tegoryStruct.comp (CommRingCat.ofHom (algebraMap (↑R) x.asIdeal.ResidueField))  
     (AlgebraicGeometry.Scheme.Spec.residueFieldIso R x).inv =     CategoryTheor
y.CategoryStruct.comp (AlgebraicGeometry.Scheme.ΓSpecIso R).inv       (CategoryT
heory.CategoryStruct.comp ((AlgebraicGeometry.Spec R).presheaf.germ ⊤ x trivial)
         ((AlgebraicGeometry.Spec R).residue x))
参数：R : CommRingCat；x : ↥(AlgebraicGeometry.Spec R)；CommRingCat.ofHom (algebraMap
 (↑R) x.asIdeal.ResidueField)；AlgebraicGeometry.Scheme.Spec.residueFieldIso R x；
AlgebraicGeometry.Scheme.ΓSpecIso R；CategoryTheory.CategoryStruct.comp ((Algebra
icGeometry.Spec R).presheaf.germ ⊤ x trivial)         ((AlgebraicGeometry.Spec R
).residue x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Spec.algebraMap_stalkIso_inv_assoc`：∀ {R : CommRingCat
} (x : PrimeSpectrum ↑R) {Z : CommRingCat} (h : (AlgebraicGeometry.Spec R).presh
eaf.stalk x ⟶ Z),   CategoryTheory.Categor…
-/
lemma Spec.algebraMap_residueFieldIso_inv :
    CommRingCat.ofHom (algebraMap R _) ≫ (residueFieldIso R x).inv =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial ≫ (Spec R).residue x := by
  rw [← Spec.algebraMap_stalkIso_inv_assoc]; rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Spec.residue_residueFieldIso_hom** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.Scheme.Spec`。
形式化陈述：∀ (R : CommRingCat) (x : ↥(AlgebraicGeometry.Spec R)),   CategoryTheory.Ca
tegoryStruct.comp ((AlgebraicGeometry.Spec R).residue x)       (AlgebraicGeometr
y.Scheme.Spec.residueFieldIso R x).hom =     CategoryTheory.CategoryStruct.comp 
(AlgebraicGeometry.Spec.stalkIso R x).hom       (CommRingCat.ofHom (algebraMap (
Localization.AtPrime x.asIdeal) x.asIdeal.ResidueField))
参数：R : CommRingCat；x : ↥(AlgebraicGeometry.Spec R)；(AlgebraicGeometry.Spec R).re
sidue x；AlgebraicGeometry.Scheme.Spec.residueFieldIso R x；AlgebraicGeometry.Spec
.stalkIso R x；CommRingCat.ofHom (algebraMap (Localization.AtPrime x.asIdeal) x.a
sIdeal.ResidueField)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
lemma Spec.residue_residueFieldIso_hom :
    (Spec R).residue x ≫ (residueFieldIso R x).hom =
      (Spec.stalkIso R x).hom ≫ CommRingCat.ofHom (algebraMap _ _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField*
* 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Spec`。
形式化陈述：∀ (R : CommRingCat) (x : ↥(AlgebraicGeometry.Spec R)),   CategoryTheory.Ca
tegoryStruct.comp       (AlgebraicGeometry.Spec.map (AlgebraicGeometry.Scheme.Sp
ec.residueFieldIso R x).inv)       (AlgebraicGeometry.Spec.map (CommRingCat.ofHo
m (algebraMap (↑R) x.asIdeal.ResidueField))) =     (AlgebraicGeometry.Spec R).fr
omSpecResidueField x
参数：R : CommRingCat；x : ↥(AlgebraicGeometry.Spec R)；AlgebraicGeometry.Spec.map (A
lgebraicGeometry.Scheme.Spec.residueFieldIso R x).inv；AlgebraicGeometry.Spec.map
 (CommRingCat.ofHom (algebraMap (↑R) x.asIdeal.ResidueField))；AlgebraicGeometry.
Spec R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `trivial`：True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Spec.fromSpecStalk_eq`：∀ (R : CommRingCat) (x : ↥(Alge
braicGeometry.Spec R)),   (AlgebraicGeometry.Spec R).fromSpecStalk x =     Algeb
raicGeometry.Spec.map       (…
· 使用定理 `AlgebraicGeometry.Spec.map_inj`：∀ {R S : CommRingCat} {φ ψ : R ⟶ S}, Alg
ebraicGeometry.Spec.map φ = AlgebraicGeometry.Spec.map ψ ↔ φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Spec.map_residueFieldIso_inv_eq_fromSpecResidueField :
    Spec.map (residueFieldIso _ _).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField)) =
    (Spec R).fromSpecResidueField x := by
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rw [Spec.map_inj]
  simp [← Scheme.Spec.algebraMap_residueFieldIso_inv]

end Spec

/-- A helper lemma to work with `AlgebraicGeometry.Scheme.SpecToEquivOfField`. -/
/-
**AlgebraicGeometry.Scheme.SpecToEquivOfField_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme`。
形式化陈述：SpecToEquivOfField_eq_iff {K : Type*} [Field K] {X : Scheme} {f₁ f₂ : Σ x 
: X.carrier, X.residueField x ⟶ .of K} : f₁ = f₂ ↔ exists e : f₁.1 = f₂.1, f₁.2 
= (X.residueFieldCongr e).hom ≫ f₂.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
A helper lemma to work with `AlgebraicGeometry.Scheme.SpecToEquivOfField`.
-/
lemma SpecToEquivOfField_eq_iff {K : Type*} [Field K] {X : Scheme}
    {f₁ f₂ : Σ x : X.carrier, X.residueField x ⟶ .of K} :
    f₁ = f₂ ↔ ∃ e : f₁.1 = f₂.1, f₁.2 = (X.residueFieldCongr e).hom ≫ f₂.2 := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨f, _⟩ := f₁
    obtain ⟨g, _⟩ := f₂
    rintro ⟨(rfl : f = g), h⟩
    simpa

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field `K` and a scheme `X`, the morphisms `Spec K ⟶ X` bijectively correspond
to pairs of points `x` of `X` and embeddings `κ(x) ⟶ K`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.SpecToEquivOfField** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：SpecToEquivOfField (K : Type u) [Field K] (X : Scheme.{u}) : (Spec (.of K)
 ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K where toFun f
参数：K : Type u；X : Scheme.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecRes
idueField`：descResidueField_stalkClosedPointTo_fromSpecResidueField (K : Type u)
 [Field K] (X : Scheme.{u}) (f : Spec (.of K) ⟶ X) : Spec.map (descResi…

--- 原说明 ---
For a field `K` and a scheme `X`, the morphisms `Spec K ⟶ X` bijectively corresp
ond
to pairs of points `x` of `X` and embeddings `κ(x) ⟶ K`.
-/
def SpecToEquivOfField (K : Type u) [Field K] (X : Scheme.{u}) :
    (Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K where
  toFun f :=
    ⟨_, X.descResidueField (Scheme.stalkClosedPointTo f)⟩
  invFun xf := Spec.map xf.2 ≫ X.fromSpecResidueField xf.1
  left_inv := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X
  right_inv f := by
    rw [SpecToEquivOfField_eq_iff]
    simp only [CommRingCat.coe_of, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
      Scheme.fromSpecResidueField_apply, exists_true_left]
    rw [← Spec.map_inj, Spec.map_comp, ← cancel_mono (X.fromSpecResidueField _)]
    grind [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField,
      Scheme.fromSpecResidueField_apply,
      Scheme.residueFieldCongr_fromSpecResidueField]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_comp** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：descResidueField_stalkClosedPointTo_comp {K : Type u} [Field K] (g : Spec 
(.of K) ⟶ X) : dsimp% descResidueField (stalkClosedPointTo (g ≫ f)) = Hom.residu
eFieldMap f (g (closedPoint K)) ≫ descResidueField (stalkClosedPointTo g)
参数：g : Spec (.of K) ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.stalkClosedPointTo_comp`：stalkClosedPointTo_com
p (g : X ⟶ Y) : stalkClosedPointTo (f ≫ g) = g.stalkMap _ ≫ stalkClosedPointTo f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.descResidueField.congr_simp`：∀ {K : Type u} [in
st : Field K] {X : AlgebraicGeometry.Scheme} {x : ↥X} (f f_1 : X.presheaf.stalk 
x ⟶ CommRingCat.of K)   (e_f : f = f_1) [i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `AlgebraicGeometry.Scheme.instEpiCommRingCatResidue`：∀ (X : AlgebraicGeom
etry.Scheme) (x : ↥X), CategoryTheory.Epi (X.residue x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.residue_descResidueField`：residue_descResidueFi
eld {K : Type u} [Field K] {X : Scheme.{u}} {x} (f : X.presheaf.stalk x ⟶ .of K)
 [IsLocalHom f.hom] : X.residue x ≫ X.d…
· 使用定理 `AlgebraicGeometry.Scheme.residue_residueFieldMap_assoc`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) (x : ↥X) {Z : CommRingCat} (h : X.residueField x 
⟶ Z),   CategoryTheory.CategoryStruct.comp (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma descResidueField_stalkClosedPointTo_comp {K : Type u} [Field K] (g : Spec (.of K) ⟶ X) :
    dsimp% descResidueField (stalkClosedPointTo (g ≫ f)) =
      Hom.residueFieldMap f (g (closedPoint K)) ≫ descResidueField (stalkClosedPointTo g) := by
  simp [← cancel_epi (Y.residue _), stalkClosedPointTo_comp, residue_residueFieldMap_assoc]

end Scheme

end AlgebraicGeometry

