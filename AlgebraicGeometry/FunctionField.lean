/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Properties

/-!
# Function field of integral schemes

We define the function field of an irreducible scheme as the stalk of the generic point.
This is a field when the scheme is integral.

## Main definition
* `AlgebraicGeometry.Scheme.functionField`: The function field of an integral scheme.
* `AlgebraicGeometry.Scheme.germToFunctionField`: The canonical map from a component into the
  function field. This map is injective.
-/

public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


universe u v

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat

namespace AlgebraicGeometry

variable (X : Scheme)

/-- The function field of an irreducible scheme is the local ring at its generic point.
Despite the name, this is a field only when the scheme is integral. -/
/-
**AlgebraicGeometry.Scheme.functionField** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → [IrreducibleSpace ↥X] → CommRingCat
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X

--- 原说明 ---
The function field of an irreducible scheme is the local ring at its generic poi
nt.
Despite the name, this is a field only when the scheme is integral.
-/
noncomputable abbrev Scheme.functionField [IrreducibleSpace X] : CommRingCat :=
  X.presheaf.stalk (genericPoint X)

/-- The restriction map from a component to the function field. -/
/-
**AlgebraicGeometry.Scheme.germToFunctionField** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) →   [inst : IrreducibleSpace ↥X] → (U : X.O
pens) → [h : Nonempty ↥↑U] → X.presheaf.obj (Opposite.op U) ⟶ X.functionField
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X

--- 原说明 ---
The restriction map from a component to the function field.
-/
noncomputable abbrev Scheme.germToFunctionField [IrreducibleSpace X] (U : X.Opens)
    [h : Nonempty U] : Γ(X, U) ⟶ X.functionField :=
  X.presheaf.germ U
    (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h))
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [IrreducibleSpace X] (U : X.Opens) [Nonempty U] :
    Algebra Γ(X, U) X.functionField :=
  (X.germToFunctionField U).hom.toAlgebra
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [IsIntegral X] : Field X.functionField :=
  (isField_stalk_of_closure_mem_irreducibleComponents X _
    (by simp [irreducibleComponents_eq_singleton])).toField
/-
**AlgebraicGeometry.germ_injective_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：germ_injective_of_isIntegral [IsIntegral X] {U : X.Opens} (x : X) (hx : x 
in U) : Function.Injective (X.presheaf.germ U x hx)
参数：x : X；hx : x in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `TopCat.Presheaf.germ_eq`：germ_eq (F : X.Presheaf C) {U V : Opens X} (x :
 X) (mU : x in U) (mV : x in V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (
op V))) (h : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `AlgebraicGeometry.map_injective_of_isIntegral`：map_injective_of_isIntegr
al [IsIntegral X] {U V : X.Opens} (i : U ⟶ V) [H : Nonempty U] : Function.Inject
ive (X.presheaf.map i.op)
-/
theorem germ_injective_of_isIntegral [IsIntegral X] {U : X.Opens} (x : X) (hx : x ∈ U) :
    Function.Injective (X.presheaf.germ U x hx) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [← (X.presheaf.germ U x hx).hom.map_zero] at hy
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ hx hx _ _ hy
  cases Subsingleton.elim iU iV
  have : Nonempty W := ⟨⟨_, hW⟩⟩
  exact map_injective_of_isIntegral X iU e
/-
**AlgebraicGeometry.Scheme.germToFunctionField_injective** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) [inst : AlgebraicGeometry.IsIntegral X] (
U : X.Opens) [inst_1 : Nonempty ↥↑U],   Function.Injective ⇑(CategoryTheory.Conc
reteCategory.hom (X.germToFunctionField U))
参数：X : AlgebraicGeometry.Scheme；U : X.Opens；CategoryTheory.ConcreteCategory.hom 
(X.germToFunctionField U)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.germ_injective_of_isIntegral`：germ_injective_of_isInte
gral [IsIntegral X] {U : X.Opens} (x : X) (hx : x in U) : Function.Injective (X.
presheaf.germ U x hx)
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
-/
theorem Scheme.germToFunctionField_injective [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  germ_injective_of_isIntegral _ _ _
/-
**AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：genericPoint_eq_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmer
sion f] [hX : IrreducibleSpace X] [IrreducibleSpace Y] : f (genericPoint X) = ge
nericPoint Y
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `IsGenericPoint.eq`：∀ {α : Type u_1} [inst : TopologicalSpace α] {x y : α
} {S : Set α} [T0Space α],   IsGenericPoint x S → IsGenericPoint y S → x = y
· 使用定理 `AlgebraicGeometry.instT0SpaceCarrierCarrierCommRingCat`：∀ (X : Algebraic
Geometry.Scheme), T0Space ↥X
· 使用定理 `genericPoint_spec`：genericPoint_spec [QuasiSober α] [IrreducibleSpace α]
 : IsGenericPoint (genericPoint α) univ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `subset_closure_inter_of_isPreirreducible_of_isOpen`：subset_closure_inter
_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsPreirreducible S) (hU : IsO
pen U) (h : (S inter U).Nonempty) : S su…
· 使用定理 `PreirreducibleSpace.isPreirreducible_univ`：∀ {X : Type u_3} {inst : Topo
logicalSpace X} [self : PreirreducibleSpace X], IsPreirreducible Set.univ
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `IrreducibleSpace.toNonempty`：∀ {X : Type u_3} {inst : TopologicalSpace X
} [self : IrreducibleSpace X], Nonempty X
· 使用定理 `trivial`：True
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `IsGenericPoint.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologica
lSpace α] [inst_1 : TopologicalSpace β] {x : α} {S : Set α},   IsGenericPoint x 
S → ∀ {f :…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
-/
theorem genericPoint_eq_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [hX : IrreducibleSpace X] [IrreducibleSpace Y] :
    f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert! (genericPoint_spec X).image f.continuous
  symm
  rw [← Set.univ_subset_iff]
  convert! subset_closure_inter_of_isPreirreducible_of_isOpen _ f.isOpenEmbedding.isOpen_range _
  · rw [Set.univ_inter, Set.image_univ]
  · apply PreirreducibleSpace.isPreirreducible_univ (X := Y)
  · exact ⟨_, trivial, Set.mem_range_self hX.2.some⟩
/-
**AlgebraicGeometry.stalkFunctionFieldAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry`。
形式化陈述：stalkFunctionFieldAlgebra [IrreducibleSpace X] (x : X) : Algebra (X.preshe
af.stalk x) X.functionField
参数：x : X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
-/
noncomputable instance stalkFunctionFieldAlgebra [IrreducibleSpace X] (x : X) :
    Algebra (X.presheaf.stalk x) X.functionField := by
  -- TODO: can we write this normally after the refactor finishes?
  apply RingHom.toAlgebra
  exact (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
/-
**AlgebraicGeometry.functionField_isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：functionField_isScalarTower [IrreducibleSpace X] (U : X.Opens) (x : U) [No
nempty U] : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField
参数：U : X.Opens；x : U。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes`：germ_stalkSpecializes (F : X.Pres
heaf C) {U : Opens X} {y : X} (hy : y in U) {x : X} (h : x ⤳ y) : F.germ U y hy 
≫ F.stalkSpecializes h = F.…
-/
instance functionField_isScalarTower [IrreducibleSpace X] (U : X.Opens) (x : U)
    [Nonempty U] : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [RingHom.algebraMap_toAlgebra]
  change _ = (X.presheaf.germ U x x.2 ≫ _).hom
  rw [X.presheaf.germ_stalkSpecializes]

@[simp]
/-
**AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) [inst : IrreducibleSpace ↥X] {U : X.Opens
} [inst_1 : Nonempty ↥↑U] {x : ↥X}   (hx : x ∈ U) (f : ↑(X.presheaf.obj (Opposit
e.op U))),   (algebraMap ↑(X.presheaf.stalk x) ↑X.functionField)       ((Categor
yTheory.ConcreteCategory.hom (X.presheaf.germ U x hx)) f) =     (CategoryTheory.
ConcreteCategory.hom (X.germToFunctionField U)) f
参数：X : AlgebraicGeometry.Scheme；hx : x ∈ U；f : ↑(X.presheaf.obj (Opposite.op U))
；algebraMap ↑(X.presheaf.stalk x) ↑X.functionField；(CategoryTheory.ConcreteCateg
ory.hom (X.presheaf.germ U x hx)) f；CategoryTheory.ConcreteCategory.hom (X.germT
oFunctionField U)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes`：germ_stalkSpecializes (F : X.Pres
heaf C) {U : Opens X} {y : X} (hy : y in U) {x : X} (h : x ⤳ y) : F.germ U y hy 
≫ F.stalkSpecializes h = F.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.algebraMap_germ_eq_germToFunctionField [IrreducibleSpace X]
    {U : X.Opens} [Nonempty U] {x : X} (hx : x ∈ U) (f : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx f) =
      X.germToFunctionField U f := by
  simp [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (R : CommRingCat.{u}) [IsDomain R] :
    Algebra R (Spec R).functionField :=
  -- TODO: can we write this normally after the refactor finishes?
  RingHom.toAlgebra <| by apply CommRingCat.Hom.hom; apply StructureSheaf.toStalk

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.genericPoint_eq_bot_of_affine** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：genericPoint_eq_bot_of_affine (R : CommRingCat) [IsDomain R] : genericPoin
t (Spec R) = (⊥ : PrimeSpectrum R)
参数：R : CommRingCat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGenericPoint.eq`：∀ {α : Type u_1} [inst : TopologicalSpace α] {x y : α
} {S : Set α} [T0Space α],   IsGenericPoint x S → IsGenericPoint y S → x = y
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `AlgebraicGeometry.instIrreducibleSpaceCarrierCarrierCommRingCatSpecOfIsD
omainCarrier`：∀ {R : CommRingCat} [IsDomain ↑R], IrreducibleSpace ↥(AlgebraicGeo
metry.Spec R)
· 使用定理 `AlgebraicGeometry.instT0SpaceCarrierCarrierCommRingCat`：∀ (X : Algebraic
Geometry.Scheme), T0Space ↥X
· 使用定理 `genericPoint_spec`：genericPoint_spec [QuasiSober α] [IrreducibleSpace α]
 : IsGenericPoint (genericPoint α) univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isGenericPoint_def`：isGenericPoint_def {x : α} {S : Set α} : IsGenericPo
int x S ↔ closure ({x} : Set α) = S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`：zeroLocus_vanishingId
eal_eq_closure (t : Set (PrimeSpectrum R)) : zeroLocus (vanishingIdeal t : Set R
) = closure t
· 使用定理 `PrimeSpectrum.vanishingIdeal_singleton`：vanishingIdeal_singleton (x : Pr
imeSpectrum R) : vanishingIdeal ({x} : Set (PrimeSpectrum R)) = x.asIdeal
· 使用定理 `PrimeSpectrum.zeroLocus_singleton_zero`：zeroLocus_singleton_zero : zeroL
ocus ({0} : Set R) = Set.univ
-/
theorem genericPoint_eq_bot_of_affine (R : CommRingCat) [IsDomain R] :
    genericPoint (Spec R) = (⊥ : PrimeSpectrum R) := by
  apply (genericPoint_spec (Spec R)).eq
  rw [isGenericPoint_def]
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.vanishingIdeal_singleton]
  rw [← PrimeSpectrum.zeroLocus_singleton_zero]
  rfl
/-
**AlgebraicGeometry.functionField_isFractionRing_of_affine** 是 Mathlib 中的一个实例，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：functionField_isFractionRing_of_affine (R : CommRingCat.{u}) [IsDomain R] 
: IsFractionRing R (Spec R).functionField
参数：R : CommRingCat.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIrreducibleSpaceCarrierCarrierCommRingCatSpecOfIsD
omainCarrier`：∀ {R : CommRingCat} [IsDomain ↑R], IrreducibleSpace ↥(AlgebraicGeo
metry.Spec R)
· 使用定理 `AlgebraicGeometry.instIsIntegralSpecOfIsDomainCarrier`：∀ {R : CommRingCa
t} [IsDomain ↑R], AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Spec R)
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Eq.to_iff`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.genericPoint_eq_bot_of_affine`：genericPoint_eq_bot_of_
affine (R : CommRingCat) [IsDomain R] : genericPoint (Spec R) = (⊥ : PrimeSpectr
um R)
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
-/
instance functionField_isFractionRing_of_affine (R : CommRingCat.{u}) [IsDomain R] :
    IsFractionRing R (Spec R).functionField := by
  convert! StructureSheaf.IsLocalization.to_stalk R (genericPoint (Spec R))
  delta IsFractionRing IsLocalization.AtPrime
  -- Porting note: `congr` does not work for `Iff`
  apply Eq.to_iff
  congr 1
  rw [genericPoint_eq_bot_of_affine]
  ext
  exact mem_nonZeroDivisors_iff_ne_zero
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme} [IsIntegral X] {U : X.Opens} [Nonempty U] :
    IsIntegral U :=
  isIntegral_of_isOpenImmersion U.ι

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsAffineOpen.primeIdealOf_genericPoint** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} [inst : AlgebraicGeometry.IsIntegral X] {
U : X.Opens}   (hU : AlgebraicGeometry.IsAffineOpen U) [h : Nonempty ↥↑U],   hU.
primeIdealOf ⟨genericPoint ↥X, ⋯⟩ = genericPoint ↥(AlgebraicGeometry.Spec (X.pre
sheaf.obj (Opposite.op U)))
参数：hU : AlgebraicGeometry.IsAffineOpen U；AlgebraicGeometry.Spec (X.presheaf.obj 
(Opposite.op U))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsGenericPoint.mem_open_set_iff`：mem_open_set_iff (h : IsGenericPoint x 
S) (hU : IsOpen U) : x in U ↔ (S inter U).Nonempty
· 使用定理 `genericPoint_spec`：genericPoint_spec [QuasiSober α] [IrreducibleSpace α]
 : IsGenericPoint (genericPoint α) univ
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `AlgebraicGeometry.instIrreducibleSpaceCarrierCarrierCommRingCatSpecOfIsD
omainCarrier`：∀ {R : CommRingCat} [IsDomain ↑R], IrreducibleSpace ↥(AlgebraicGeo
metry.Spec R)
· 使用定理 `AlgebraicGeometry.IsIntegral.component_integral`：∀ {X : AlgebraicGeometr
y.Scheme} [self : AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty ↥↑U], 
  IsDomain ↑(X.presheaf.obj (Opposite…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding_obj_top`：isOpenEmbedding_obj_top 
{X : TopCat.{u}} (U : Opens X) : U.isOpenEmbedding.functor.obj ⊤ = U
· 使用定理 `AlgebraicGeometry.instIsIntegralToSchemeOfNonemptyCarrierCarrierCommRing
Cat`：∀ {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsIntegral X] {U : X.Op
ens} [Nonempty ↥↑U],   AlgebraicGeometry.IsIntegral ↑U
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion`：genericPoint_eq_of
_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] [hX : Irreducibl
eSpace X] [IrreducibleSpace Y] : f (generi…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.instIsIsoSchemeMapOfCommRingCat`：∀ {R S : CommRingCat}
 (f : R ⟶ S) [CategoryTheory.IsIso f], CategoryTheory.IsIso (AlgebraicGeometry.S
pec.map f)
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
-/
theorem IsAffineOpen.primeIdealOf_genericPoint {X : Scheme} [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) [h : Nonempty U] :
    hU.primeIdealOf
        ⟨genericPoint X,
          ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h)⟩ =
      genericPoint (Spec Γ(X, U)) := by
  delta IsAffineOpen.primeIdealOf
  convert!
    genericPoint_eq_of_isOpenImmersion
      (U.toScheme.isoSpec.hom ≫ Spec.map (X.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op))
        -- Porting note: this was `ext1`

  -- Porting note: this was `ext1`
  apply Subtype.ext
  exact (genericPoint_eq_of_isOpenImmersion U.ι).symm
/-
**AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：functionField_isFractionRing_of_isAffineOpen [IsIntegral X] (U : X.Opens) 
(hU : IsAffineOpen U) [Nonempty U] : IsFractionRing Γ(X, U) X.functionField
参数：U : X.Opens；hU : IsAffineOpen U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsGenericPoint.mem_open_set_iff`：mem_open_set_iff (h : IsGenericPoint x 
S) (hU : IsOpen U) : x in U ↔ (S inter U).Nonempty
· 使用定理 `genericPoint_spec`：genericPoint_spec [QuasiSober α] [IrreducibleSpace α]
 : IsGenericPoint (genericPoint α) univ
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `AlgebraicGeometry.instIrreducibleSpaceCarrierCarrierCommRingCatSpecOfIsD
omainCarrier`：∀ {R : CommRingCat} [IsDomain ↑R], IrreducibleSpace ↥(AlgebraicGeo
metry.Spec R)
· 使用定理 `AlgebraicGeometry.IsIntegral.component_integral`：∀ {X : AlgebraicGeometr
y.Scheme} [self : AlgebraicGeometry.IsIntegral X] (U : X.Opens) [Nonempty ↥↑U], 
  IsDomain ↑(X.presheaf.obj (Opposite…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.primeIdealOf_genericPoint`：∀ {X : Algebra
icGeometry.Scheme} [inst : AlgebraicGeometry.IsIntegral X] {U : X.Opens}   (hU :
 AlgebraicGeometry.IsAffineOpen U) [h : Nonemp…
· 使用定理 `AlgebraicGeometry.genericPoint_eq_bot_of_affine`：genericPoint_eq_bot_of_
affine (R : CommRingCat) [IsDomain R] : genericPoint (Spec R) = (⊥ : PrimeSpectr
um R)
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `AlgebraicGeometry.Scheme.component_nontrivial`：∀ (X : AlgebraicGeometry.
Scheme) (U : X.Opens) [Nonempty ↥↑U], Nontrivial ↑(X.presheaf.obj (Opposite.op U
))
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`：isLocalization_stal
k (x : U) : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asId
eal
-/
theorem functionField_isFractionRing_of_isAffineOpen [IsIntegral X] (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField := by
  delta IsFractionRing Scheme.functionField
  convert!
    hU.isLocalization_stalk
      ⟨genericPoint X,
        (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))⟩
    using 1
  rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  ext; exact mem_nonZeroDivisors_iff_ne_zero
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : X) : IsAffine (X.affineCover.X x) :=
  AlgebraicGeometry.isAffine_Spec _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIntegral X] (x : X) :
    IsFractionRing (X.presheaf.stalk x) X.functionField :=
  let U : X.Opens := (X.affineCover.f ((X.affineCover.idx x))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let x : U := ⟨x, X.affineCover.covers x⟩
  have : Nonempty U := ⟨x⟩
  let M := (hU.primeIdealOf x).asIdeal.primeCompl
  have := hU.isLocalization_stalk x
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  -- Porting note: the following two lines were not needed.
  let _hA := Presheaf.algebra_section_stalk X.presheaf x
  have := functionField_isScalarTower X U x
  .isFractionRing_of_isDomain_of_isLocalization M ↑(Presheaf.stalk X.presheaf x)
    (Scheme.functionField X)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIntegral X] {x : X} : IsDomain (X.presheaf.stalk x) :=
  Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk x) (X.functionField))

/--
For `f` an element of the function field of `X`, there exists some open set `U ⊆ X` such that
`f` is a unit in `Γ(X, U)`.
-/
/-
**AlgebraicGeometry.exists_isUnit_germ_eq** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：exists_isUnit_germ_eq [IsIntegral X] (f : X.functionField) (hf : f != 0) :
 exists U in X.affineOpens, exists f' : Γ(X, U), exists _ : Nonempty U, X.germTo
FunctionField U f' = f ∧ IsUnit f'
参数：f : X.functionField；hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …
· 使用定理 `AlgebraicGeometry.Scheme.mem_basicOpen`：mem_basicOpen (x : X) (hx : x in
 U) : x in X.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f)
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`：isUnit_res_basicOpen
 {U : Opens X} (f : X.presheaf.obj (op U)) : IsUnit (X.presheaf.map (@homOfLE (O
pens X) _ _ _ (X.basicOpen_le f)).op f)

--- 原说明 ---
For `f` an element of the function field of `X`, there exists some open set `U ⊆
 X` such that
`f` is a unit in `Γ(X, U)`.
-/
lemma exists_isUnit_germ_eq [IsIntegral X] (f : X.functionField) (hf : f ≠ 0) :
    ∃ U ∈ X.affineOpens, ∃ f' : Γ(X, U), ∃ _ : Nonempty U,
      X.germToFunctionField U f' = f ∧ IsUnit f' := by
  obtain ⟨U, hU, g, hg⟩ := X.presheaf.exists_germ_eq f
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  have : Nonempty A := ⟨_, hxA⟩
  let gA : Γ(X, A) := X.presheaf.map (homOfLE hAU).op g
  have h_germ_gA : X.presheaf.germ A (genericPoint X) hxA gA = f := by
    simp only [← hg, ← X.presheaf.germ_res_apply (homOfLE hAU) (genericPoint X) hxA g, gA]
    rfl
  have hxV : genericPoint X ∈ X.basicOpen gA := by
    rwa [Scheme.mem_basicOpen X gA (genericPoint X) hxA, h_germ_gA, isUnit_iff_ne_zero]
  have : Nonempty (X.basicOpen gA) := ⟨⟨_, hxV⟩⟩
  refine ⟨X.basicOpen gA, hA.basicOpen gA,
    X.presheaf.map (X.basicOpen_le gA).hom.op gA, ‹_›, ?_,
    X.toRingedSpace.isUnit_res_basicOpen gA⟩
  simpa using h_germ_gA

end AlgebraicGeometry

