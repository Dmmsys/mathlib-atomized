/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.Opposite

/-!
# The homotopy fiber of a morphism of homological complexes

In this file, we construct the homotopy fiber of a morphism `φ : F ⟶ G`
between homological complexes. Moreover, we dualise the definition
of the cylinder (which is a particular case of a homotopy cofiber)
in order to define the path object of a homological complex.

-/

@[expose] public section

open CategoryTheory Category Limits Preadditive Opposite

variable {C : Type*} [Category* C] [Preadditive C]

namespace HomologicalComplex

attribute [local instance] ComplexShape.decidableRelSymm

variable {α : Type*} {c : ComplexShape α} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [DecidableRel c.Rel]

section

/-- A morphism of homological complexes `φ : F ⟶ G` has a homotopy fiber if for all
indices `i` and `j` such that `c.Rel i j`, the binary biproduct `F.X i ⊞ G.X j` exists. -/
/-
**HomologicalComplex.HasHomotopyFiber** 是 Mathlib 中的一个归纳类型，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {α : Type u_2} → {c : ComplexShape 
α} → {F G : HomologicalComplex C c} → (F ⟶ G) → Prop
参数：F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of homological complexes `φ : F ⟶ G` has a homotopy fiber if for all
indices `i` and `j` such that `c.Rel i j`, the binary biproduct `F.X i ⊞ G.X j` 
exists.
-/
class HasHomotopyFiber (φ : F ⟶ G) : Prop where
  hasBinaryBiproduct (φ) (i j : α) (hij : c.Rel i j) : HasBinaryBiproduct (G.X i) (F.X j)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasBinaryBiproducts C] : HasHomotopyFiber φ where
  hasBinaryBiproduct _ _ _ := inferInstance

variable [HasHomotopyFiber φ]

set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasHomotopyCofiber ((opFunctor C c).map φ.op) where
  hasBinaryBiproduct i j hij := by
    have := HasHomotopyFiber.hasBinaryBiproduct φ j i hij
    dsimp
    infer_instance

/-- The homotopy fiber of a morphism between homological complexes. -/
/-
**HomologicalComplex.homotopyFiber** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：homotopyFiber : HomologicalComplex C c
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomotopyCofiberOppositeMapSymmOpFunctorOp`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C] {α : Type u_2}   {c : ComplexShape α}…

--- 原说明 ---
The homotopy fiber of a morphism between homological complexes.
-/
noncomputable def homotopyFiber : HomologicalComplex C c :=
  (unopFunctor C c.symm).obj (op (homotopyCofiber ((opFunctor C c).map φ.op)))

end

variable (K) [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]

set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : α) : HasBinaryBiproduct (K.op.X i) (K.op.X i) := by
  dsimp; infer_instance

/-- The property that a homological complex `K` has a path object,
i.e. that the morphism `K ⟶ K ⊞ K` induced by `𝟙 K` and `-𝟙 K`
has a homotopy fiber. -/
/-
**HomologicalComplex.HasPathObject** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：HasPathObject
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…

--- 原说明 ---
The property that a homological complex `K` has a path object,
i.e. that the morphism `K ⟶ K ⊞ K` induced by `𝟙 K` and `-𝟙 K`
has a homotopy fiber.
-/
abbrev HasPathObject := HasHomotopyFiber (biprod.desc (𝟙 K) (-𝟙 K))
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [K.HasPathObject] :
    HasHomotopyCofiber (biprod.lift (𝟙 K.op) (-𝟙 K.op)) where
  hasBinaryBiproduct i j hij := by
    have := HasHomotopyFiber.hasBinaryBiproduct (biprod.desc (𝟙 K) (-𝟙 K)) j i hij
    exact hasBinaryBiproduct_of_iso (Iso.refl _ : op (K.X j) ≅ K.op.X j)
      (show op ((K ⊞ K).X i) ≅ (K.op ⊞ K.op).X i from
        ((eval _ _ i).mapBiprod K K).op.symm ≪≫ biprod.opIso _ _ ≪≫
          ((eval _ _ i).mapBiprod K.op K.op).symm)

variable [K.HasPathObject]

/-- The path object of a homological complex is defined here by dualizing
the cylinder object of `K.op`. -/
@[no_expose]
/-
**HomologicalComplex.pathObject** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：pathObject
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproductOppositeXOp`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditiv
e C] {α : Type u_2}   {c : ComplexShape α}…
· 使用定理 `HomologicalComplex.instHasHomotopyCofiberOppositeLiftSymmIdOpNegHomOfHas
PathObject`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst
_1 : CategoryTheory.Preadditive C] {α : Type u_2}   {c : ComplexShape α}…

--- 原说明 ---
The path object of a homological complex is defined here by dualizing
the cylinder object of `K.op`.
-/
noncomputable def pathObject := (unopFunctor C c.symm).obj (op K.op.cylinder)

namespace pathObject

set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.pathObject.isZero_X** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalC
omplex.pathObject`。
形式化陈述：isZero_X (i : α) (h₁ : IsZero (K.X i)) (h₂ : forall (j : α), c.Rel j i -> 
IsZero (K.X j)) : IsZero (K.pathObject.X i)
参数：i : α；h₁ : IsZero (K.X i)；h₂ : forall (j : α), c.Rel j i -> IsZero (K.X j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.unop`：unop {X : Cᵒᵖ} (h : IsZero X) : IsZer
o (Opposite.unop X)
· 使用引理 `HomologicalComplex.homotopyCofiber.isZero_X`：isZero_X (i : ι) (hG : IsZe
ro (G.X i)) (hF : forall (j : ι), c.Rel i j -> IsZero (F.X j)) : IsZero (X φ i)
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `HomologicalComplex.instHasBinaryBiproductOppositeXOp`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditiv
e C] {α : Type u_2}   {c : ComplexShape α}…
· 使用定理 `HomologicalComplex.instHasHomotopyCofiberOppositeLiftSymmIdOpNegHomOfHas
PathObject`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst
_1 : CategoryTheory.Preadditive C] {α : Type u_2}   {c : ComplexShape α}…
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `HomologicalComplex.instPreservesBinaryBiproductEval`：∀ {C : Type u_1} {ι
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryThe
ory.Preadditive C]   {c : ComplexShape ι}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `CategoryTheory.Limits.IsZero.op`：op (h : IsZero X) : IsZero (Opposite.op
 X)
-/
lemma isZero_X (i : α) (h₁ : IsZero (K.X i)) (h₂ : ∀ (j : α), c.Rel j i → IsZero (K.X j)) :
    IsZero (K.pathObject.X i) := by
  apply IsZero.unop
  dsimp [pathObject]
  refine homotopyCofiber.isZero_X _ _ ?_ (fun j hj ↦ IsZero.op (h₂ _ hj))
  exact IsZero.of_iso (by simpa using h₁.op)
    ((eval Cᵒᵖ c.symm i).mapBiprod K.op K.op)

/-- The first projection `K.pathObject ⟶ K`. -/
@[no_expose]
/-
**HomologicalComplex.pathObject.** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.p
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection `K.pathObject ⟶ K`.
-/
noncomputable def π₀ : K.pathObject ⟶ K :=
  (unopFunctor C c.symm).map (cylinder.ι₀ K.op).op

/-- The second projection `K.pathObject ⟶ K`. -/
@[no_expose]
/-
**HomologicalComplex.pathObject.** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.p
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection `K.pathObject ⟶ K`.
-/
noncomputable def π₁ : K.pathObject ⟶ K :=
  (unopFunctor C c.symm).map (cylinder.ι₁ K.op).op

/-- The inclusion `K ⟶ K.pathObject`. -/
@[no_expose]
/-
**HomologicalComplex.pathObject.** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.p
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `K ⟶ K.pathObject`.
-/
noncomputable def ι : K ⟶ K.pathObject :=
  (unopFunctor C c.symm).map (cylinder.π K.op).op

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pathObject.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex.p
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π₀_ι : ι K ≫ π₀ K = 𝟙 K :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_π K.op))

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pathObject.** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex.p
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π₁_ι : ι K ≫ π₁ K = 𝟙 K :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_π K.op))

/-- The homotopy between `π₀ K ≫ ι K` and `𝟙 K.pathObject`. -/
@[no_expose]
/-
**HomologicalComplex.pathObject.** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex.p
athObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy between `π₀ K ≫ ι K` and `𝟙 K.pathObject`.
-/
noncomputable def π₀CompιHomotopy (hc : ∀ (i : α), ∃ j, c.Rel i j) :
    Homotopy (π₀ K ≫ ι K) (𝟙 K.pathObject) :=
  (cylinder.πCompι₀Homotopy K.op hc).unop

/-- The homotopy equivalence between `K` and `K.pathObject`. -/
@[simps]
/-
**HomologicalComplex.pathObject.homotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Homolog
icalComplex.pathObject`。
形式化陈述：homotopyEquiv (hc : forall (i : α), exists j, c.Rel i j) : HomotopyEquiv K
 K.pathObject where hom
参数：hc : forall (i : α), exists j, c.Rel i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy equivalence between `K` and `K.pathObject`.
-/
noncomputable def homotopyEquiv (hc : ∀ (i : α), ∃ j, c.Rel i j) :
    HomotopyEquiv K K.pathObject where
  hom := ι K
  inv := π₀ K
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := π₀CompιHomotopy K hc

/-- The homotopy between `pathObject.ι₀ K` and `pathObject.ι₁ K`. -/
@[no_expose]
/-
**HomologicalComplex.pathObject.homotopy** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalC
omplex.pathObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy between `pathObject.ι₀ K` and `pathObject.ι₁ K`.
-/
noncomputable def homotopy₀₁ (hc : ∀ (i : α), ∃ j, c.Rel i j) : Homotopy (π₀ K) (π₁ K) :=
  (cylinder.homotopy₀₁ K.op hc).unop

section

variable {K} (φ₀ φ₁ : F ⟶ K) (h : Homotopy φ₀ φ₁)

/-- The morphism `F ⟶ K.pathObject` that is induced by two morphisms `φ₀ φ₁ : F ⟶ K`
and a homotopy `h : Homotopy φ₀ φ₁`. -/
@[no_expose]
/-
**HomologicalComplex.pathObject.lift** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex.pathObject`。
形式化陈述：lift : F ⟶ K.pathObject
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasBinaryBiproductOppositeXOp`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditiv
e C] {α : Type u_2}   {c : ComplexShape α}…
· 使用定理 `HomologicalComplex.instHasHomotopyCofiberOppositeLiftSymmIdOpNegHomOfHas
PathObject`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst
_1 : CategoryTheory.Preadditive C] {α : Type u_2}   {c : ComplexShape α}…

--- 原说明 ---
The morphism `F ⟶ K.pathObject` that is induced by two morphisms `φ₀ φ₁ : F ⟶ K`
and a homotopy `h : Homotopy φ₀ φ₁`.
-/
noncomputable def lift : F ⟶ K.pathObject :=
  letI φ : K.op.cylinder ⟶ (opFunctor C c).obj (op F) :=
    cylinder.desc ((opFunctor C c).map φ₀.op)
      ((opFunctor C c).map φ₁.op) h.op
  (unopFunctor C c.symm).map φ.op

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pathObject.lift_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex.pathObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_π₀ : lift φ₀ φ₁ h ≫ π₀ K = φ₀ :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₀_desc _ _ _))

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pathObject.lift_** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComp
lex.pathObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_π₁ : lift φ₀ φ₁ h ≫ π₁ K = φ₁ :=
  Quiver.Hom.op_inj ((opFunctor C c).map_injective (cylinder.ι₁_desc _ _ _))

end

section

variable (F) {D : Type*} [Category* D] [Preadditive D] (H : C ⥤ D) [H.Additive]
  [∀ (i : α), HasBinaryBiproduct (((H.mapHomologicalComplex c).obj K).X i)
    (((H.mapHomologicalComplex c).obj K).X i)]
  [((H.mapHomologicalComplex c).obj K).HasPathObject]

variable
  [∀ (i : α),
    HasBinaryBiproduct (((H.op.mapHomologicalComplex c.symm).obj K.op).X i)
      (((H.op.mapHomologicalComplex c.symm).obj K.op).X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 ((H.op.mapHomologicalComplex c.symm).obj K.op))
    (-𝟙 ((H.op.mapHomologicalComplex c.symm).obj K.op)))]
  [HasHomotopyCofiber ((H.op.mapHomologicalComplex c.symm).map (biprod.lift (𝟙 K.op) (-𝟙 K.op)))]
  [∀ (i : α), HasBinaryBiproduct (K.op.X i) (K.op.X i)]

variable (hc : ∀ (i : α), ∃ j, c.Rel i j)

/-- The isomorphism expressing the commutation between taking
the path object of a homological complex and applying an additive functor. -/
@[no_expose]
/-
**HomologicalComplex.pathObject.mapHomologicalComplexObjIso** 是 Mathlib 中的一个定义，位
于命名空间 `HomologicalComplex.pathObject`。
形式化陈述：mapHomologicalComplexObjIso : (H.mapHomologicalComplex c).obj (K.pathObjec
t) ≅ pathObject ((H.mapHomologicalComplex c).obj K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomologicalComplex.instHasHomotopyCofiberOppositeLiftSymmIdOpNegHomOfHas
PathObject`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst
_1 : CategoryTheory.Preadditive C] {α : Type u_2}   {c : ComplexShape α}…
· 使用定理 `CategoryTheory.Functor.op_additive`：∀ {C : Type u_1} [inst : CategoryThe
ory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] {D : Type u_2
}   [inst_2 : CategoryTh…

--- 原说明 ---
The isomorphism expressing the commutation between taking
the path object of a homological complex and applying an additive functor.
-/
noncomputable def mapHomologicalComplexObjIso :
    (H.mapHomologicalComplex c).obj (K.pathObject) ≅
      pathObject ((H.mapHomologicalComplex c).obj K) :=
  (unopFunctor _ _).mapIso (cylinder.mapHomologicalComplexObjIso K.op H.op hc).op.symm

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pathObject.mapHomologicalComplexObjIso_inv_map_** 是 Mathlib
 中的一个引理，位于命名空间 `HomologicalComplex.pathObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapHomologicalComplexObjIso_inv_map_π₀ :
    (mapHomologicalComplexObjIso K H hc).inv ≫ (H.mapHomologicalComplex c).map (π₀ K) =
      π₀ _ :=
  Quiver.Hom.op_inj ((opFunctor _ _).map_injective
    (cylinder.map_ι₀_mapHomologicalComplexObjIso_hom K.op H.op hc))

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pathObject.mapHomologicalComplexObjIso_inv_map_** 是 Mathlib
 中的一个引理，位于命名空间 `HomologicalComplex.pathObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapHomologicalComplexObjIso_inv_map_π₁ :
    (mapHomologicalComplexObjIso K H hc).inv ≫ (H.mapHomologicalComplex c).map (π₁ K) =
      π₁ _ :=
  Quiver.Hom.op_inj ((opFunctor _ _).map_injective
    (cylinder.map_ι₁_mapHomologicalComplexObjIso_hom K.op H.op hc))

end

end pathObject

end HomologicalComplex

