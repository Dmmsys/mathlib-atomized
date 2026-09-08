/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao, Jujian Zhang
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!

# Galois Group as a profinite group

In this file, we prove that given a field extension `K/k`, there is a continuous isomorphism between
`Gal(K/k)` and the limit of `Gal(L/k)`, where `L` is a finite Galois intermediate field ordered by
inverse inclusion, thus making `Gal(K/k)` profinite as a limit of finite groups.

## Main definitions and results

In a field extension `K/k`

* `finGaloisGroup L` : The (finite) Galois group `Gal(L/k)` associated to a
  `L : FiniteGaloisIntermediateField k K` `L`.

* `finGaloisGroupMap` : For `FiniteGaloisIntermediateField` s `L₁` and `L₂` with `L₂ ≤ L₁`
  giving the restriction of `Gal(L₁/k)` to `Gal(L₂/k)`

* `finGaloisGroupFunctor` : The functor from `FiniteGaloisIntermediateField`
  (ordered by reverse inclusion) to `FiniteGrp`, mapping each `FiniteGaloisIntermediateField L`
  to `Gal (L/k)`.

* `InfiniteGalois.algEquivToLimit` : The homomorphism from `Gal(K/k)` to
  `limit (asProfiniteGaloisGroupFunctor k K)`, induced by the projections from `Gal(K/k)` to
  any `Gal(L/k)` where `L` is a `FiniteGaloisIntermediateField`.

* `InfiniteGalois.limitToAlgEquiv` : The inverse of `InfiniteGalois.algEquivToLimit`, in which
  the elements of `Gal(K/k)` are constructed pointwise.

* `InfiniteGalois.mulEquivToLimit` : The mulEquiv obtained from combining the above two.

* `InfiniteGalois.mulEquivToLimit_continuous` : The inverse of `InfiniteGalois.mulEquivToLimit`
  is continuous.

* `InfiniteGalois.continuousMulEquivToLimit` ：The `ContinuousMulEquiv` between `Gal(K/k)` and
  `limit (asProfiniteGaloisGroupFunctor k K)` given by `InfiniteGalois.mulEquivToLimit`

* `InfiniteGalois.ProfiniteGalGrp` : `Gal(K/k)` as a profinite group as there is
  a `ContinuousMulEquiv` to a `ProfiniteGrp` given above.

* `InfiniteGalois.restrictNormalHomContinuous` : Any `restrictNormalHom` is continuous.

-/

@[expose] public section

open CategoryTheory Opposite

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Profinite

/-- The (finite) Galois group `Gal(L / k)` associated to a
`L : FiniteGaloisIntermediateField k K` `L`. -/
/-
**FiniteGaloisIntermediateField.finGaloisGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FiniteGaloisIntermediateField.finGaloisGroup (L : FiniteGaloisIntermediate
Field k K) : FiniteGrp
参数：L : FiniteGaloisIntermediateField k K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (finite) Galois group `Gal(L / k)` associated to a
`L : FiniteGaloisIntermediateField k K` `L`.
-/
def FiniteGaloisIntermediateField.finGaloisGroup (L : FiniteGaloisIntermediateField k K) :
    FiniteGrp :=
  letI := AlgEquiv.fintype k L
  FiniteGrp.of Gal(L/k)

/-- For `FiniteGaloisIntermediateField` s `L₁` and `L₂` with `L₂ ≤ L₁`
  the restriction homomorphism from `Gal(L₁/k)` to `Gal(L₂/k)` -/
/-
**finGaloisGroupMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finGaloisGroupMap {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ} (le : L₁
 ⟶ L₂) : L₁.unop.finGaloisGroup ⟶ L₂.unop.finGaloisGroup
参数：FiniteGaloisIntermediateField k K；le : L₁ ⟶ L₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `FiniteGaloisIntermediateField` s `L₁` and `L₂` with `L₂ ≤ L₁`
  the restriction homomorphism from `Gal(L₁/k)` to `Gal(L₂/k)`
-/
noncomputable def finGaloisGroupMap {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (le : L₁ ⟶ L₂) : L₁.unop.finGaloisGroup ⟶ L₂.unop.finGaloisGroup :=
  haveI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom le.1)
  haveI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  FiniteGrp.ofHom (AlgEquiv.restrictNormalHom L₂.unop)

namespace finGaloisGroupMap

@[simp]
/-
**finGaloisGroupMap.map_id** 是 Mathlib 中的一个引理，位于命名空间 `finGaloisGroupMap`。
形式化陈述：map_id (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) : (finGaloisGroupMap (𝟙
 L)) = 𝟙 L.unop.finGaloisGroup
参数：L : (FiniteGaloisIntermediateField k K)ᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `AlgEquiv.restrictNormalHom_id`：AlgEquiv.restrictNormalHom_id (F K : Type
*) [Field F] [Field K] [Algebra F K] [Normal F K] : AlgEquiv.restrictNormalHom K
 = MonoidHom.id Gal…
-/
lemma map_id (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) :
    (finGaloisGroupMap (𝟙 L)) = 𝟙 L.unop.finGaloisGroup :=
  ConcreteCategory.ext (AlgEquiv.restrictNormalHom_id _ _)

@[simp]
/-
**finGaloisGroupMap.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `finGaloisGroupMap`。
形式化陈述：map_comp {L₁ L₂ L₃ : (FiniteGaloisIntermediateField k K)ᵒᵖ} (f : L₁ ⟶ L₂) 
(g : L₂ ⟶ L₃) : finGaloisGroupMap (f ≫ g) = finGaloisGroupMap f ≫ finGaloisGroup
Map g
参数：FiniteGaloisIntermediateField k K；f : L₁ ⟶ L₂；g : L₂ ⟶ L₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `IsScalarTower.AlgEquiv.restrictNormalHom_comp`：∀ (F : Type u_6) (K₁ : Ty
pe u_7) (K₂ : Type u_8) (K₃ : Type u_9) [inst : Field F] [inst_1 : Field K₁]   [
inst_2 : Field K₂] [inst_3 : Field …
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
-/
lemma map_comp {L₁ L₂ L₃ : (FiniteGaloisIntermediateField k K)ᵒᵖ} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) :
    finGaloisGroupMap (f ≫ g) = finGaloisGroupMap f ≫ finGaloisGroupMap g := by
  iterate 2
    induction L₁ with | _ L₁ => ?_
    induction L₂ with | _ L₂ => ?_
    induction L₃ with | _ L₃ => ?_
  algebraize [Subsemiring.inclusion g.unop.le, Subsemiring.inclusion f.unop.le,
    Subsemiring.inclusion (g.unop.le.trans f.unop.le)]
  have : IsScalarTower k L₂ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k L₃ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k L₃ L₂ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower L₃ L₂ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  ext : 1
  apply IsScalarTower.AlgEquiv.restrictNormalHom_comp k L₃ L₂ L₁

end finGaloisGroupMap

variable (k K) in
/-- The functor from `FiniteGaloisIntermediateField` (ordered by reverse inclusion) to `FiniteGrp`,
mapping each `FiniteGaloisIntermediateField` `L` to `Gal (L/k)` -/
/-
**finGaloisGroupFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finGaloisGroupFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp 
where obj L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `finGaloisGroupMap.map_id`：map_id (L : (FiniteGaloisIntermediateField k K
)ᵒᵖ) : (finGaloisGroupMap (𝟙 L)) = 𝟙 L.unop.finGaloisGroup
· 使用引理 `finGaloisGroupMap.map_comp`：map_comp {L₁ L₂ L₃ : (FiniteGaloisIntermedia
teField k K)ᵒᵖ} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) : finGaloisGroupMap (f ≫ g) = finGal
oisGroupMap f ≫ …

--- 原说明 ---
The functor from `FiniteGaloisIntermediateField` (ordered by reverse inclusion) 
to `FiniteGrp`,
mapping each `FiniteGaloisIntermediateField` `L` to `Gal (L/k)`
-/
noncomputable def finGaloisGroupFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp where
  obj L := L.unop.finGaloisGroup
  map := finGaloisGroupMap
  map_id := finGaloisGroupMap.map_id
  map_comp := finGaloisGroupMap.map_comp

open FiniteGaloisIntermediateField ProfiniteGrp

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

variable (k K) in
/-- The composition of `finGaloisGroupFunctor` with
the forgetful functor from `FiniteGrp` to `ProfiniteGrp`. -/
/-
**InfiniteGalois.asProfiniteGaloisGroupFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `Infi
niteGalois`。
形式化陈述：asProfiniteGaloisGroupFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ Pr
ofiniteGrp
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of `finGaloisGroupFunctor` with
the forgetful functor from `FiniteGrp` to `ProfiniteGrp`.
-/
noncomputable abbrev asProfiniteGaloisGroupFunctor :
    (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ ProfiniteGrp :=
  (finGaloisGroupFunctor k K) ⋙ forget₂ FiniteGrp ProfiniteGrp

variable (k K) in
/--
The homomorphism from `Gal(K/k)` to `lim Gal(L/k)` where `L` is a
`FiniteGaloisIntermediateField k K` ordered by inverse inclusion. It is induced by the
canonical projections from `Gal(K/k)` to `Gal(L/k)`.
-/
/-
**InfiniteGalois.algEquivToLimit** 是 Mathlib 中的一个定义，位于命名空间 `InfiniteGalois`。
形式化陈述：algEquivToLimit : Gal(K/k) ->* limit (asProfiniteGaloisGroupFunctor k K) w
here toFun σ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism from `Gal(K/k)` to `lim Gal(L/k)` where `L` is a
`FiniteGaloisIntermediateField k K` ordered by inverse inclusion. It is induced 
by the
canonical projections from `Gal(K/k)` to `Gal(L/k)`.
-/
noncomputable def algEquivToLimit : Gal(K/k) →* limit (asProfiniteGaloisGroupFunctor k K) where
  toFun σ := {
    val := fun L ↦ σ.restrictNormalHom L.unop
    property := fun {L₁ L₂} π ↦ by
      algebraize [Subsemiring.inclusion π.1.le]
      have : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      have : IsScalarTower L₂.unop L₁.unop K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      apply (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L₂.unop L₁.unop σ).symm }
  map_one' := by
    simp only [map_one]
    rfl
  map_mul' x y := by
    simp only [map_mul]
    rfl
/-
**InfiniteGalois.restrictNormalHom_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Infinit
eGalois`。
形式化陈述：restrictNormalHom_continuous (L : IntermediateField k K) [Normal k L] : Co
ntinuous (AlgEquiv.restrictNormalHom (F
参数：L : IntermediateField k K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_continuousAt_one`：continuous_of_continuousAt_one {M hom : 
Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] [FunLike hom G M] 
[MonoidHomClass hom …
· 使用定理 `instIsTopologicalGroupAlgEquiv`：∀ (K : Type u_1) (L : Type u_2) [inst : 
Field K] [inst_1 : Field L] [inst_2 : Algebra K L], IsTopologicalGroup Gal(L/K)
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_def`：continuousAt_def : ContinuousAt f x ↔ forall A in 𝓝 (f
 x), f ⁻¹' A in 𝓝 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `krullTopology_mem_nhds_one_iff`：krullTopology_mem_nhds_one_iff (K L : Ty
pe*) [Field K] [Field L] [Algebra K L] (s : Set Gal(L/K)) : s in 𝓝 1 ↔ exists E 
: IntermediateField …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.coe_eq_coe`：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
· 使用定理 `IntermediateField.mem_lift`：mem_lift {F : IntermediateField K L} {E : In
termediateField K F} (x : F) : x.1 in lift E ↔ x in E
· 使用定理 `IntermediateField.fixingSubgroup_isOpen`：IntermediateField.fixingSubgrou
p_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField 
K L) [FiniteDimensional K E] …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem restrictNormalHom_continuous (L : IntermediateField k K) [Normal k L] :
    Continuous (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) L) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨L', _, hO⟩ := hN
  have := Module.Finite.equiv <| AlgEquiv.toLinearEquiv <| IntermediateField.liftAlgEquiv L'
  apply mem_nhds_iff.mpr
  use (IntermediateField.lift L').fixingSubgroup
  constructor
  · intro x hx
    apply hO
    simp only [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hx ⊢
    intro y hy
    have := AlgEquiv.restrictNormal_commutes x L y
    dsimp at this
    rw [hx y.1 ((IntermediateField.mem_lift y).mpr hy)] at this
    exact SetLike.coe_eq_coe.mp this
  · exact ⟨IntermediateField.fixingSubgroup_isOpen (IntermediateField.lift L'), congrFun rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-
**InfiniteGalois.algEquivToLimit_continuous** 是 Mathlib 中的一个引理，位于命名空间 `InfiniteG
alois`。
形式化陈述：algEquivToLimit_continuous : Continuous (algEquivToLimit k K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateField`：∀
 (k : Type u_1) (K : Type u_2) [inst : Field k] [inst_1 : Field K] [inst_2 : Alg
ebra k K]   (L : FiniteGaloisIntermediateField k K), IsGalo…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `DiscreteTopology.eq_bot`：∀ {α : Type u_2} {t : TopologicalSpace α} [self
 : DiscreteTopology α], t = ⊥
· 使用定理 `FiniteGaloisIntermediateField.instFiniteDimensionalSubtypeMemIntermediat
eField`：∀ (k : Type u_1) (K : Type u_2) [inst : Field k] [inst_1 : Field K] [ins
t_2 : Algebra k K]   (L : FiniteGaloisIntermediateField k K), Finite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `InfiniteGalois.restrictNormalHom_continuous`：restrictNormalHom_continuou
s (L : IntermediateField k K) [Normal k L] : Continuous (AlgEquiv.restrictNormal
Hom (F
-/
lemma algEquivToLimit_continuous : Continuous (algEquivToLimit k K) := by
  rw [continuous_induced_rng]
  refine continuous_pi (fun L ↦ ?_)
  convert! restrictNormalHom_continuous L.unop.1
  exact (DiscreteTopology.eq_bot (α := L.unop ≃ₐ[k] L.unop)).symm

/-- The projection map from `lim Gal(L/k)` to a specific `Gal(L/k)`. -/
/-
**InfiniteGalois.proj** 是 Mathlib 中的一个定义，位于命名空间 `InfiniteGalois`。
形式化陈述：proj (L : FiniteGaloisIntermediateField k K) : limit (asProfiniteGaloisGro
upFunctor k K) ->* Gal(L/k) where toFun g
参数：L : FiniteGaloisIntermediateField k K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map from `lim Gal(L/k)` to a specific `Gal(L/k)`.
-/
noncomputable def proj (L : FiniteGaloisIntermediateField k K) :
    limit (asProfiniteGaloisGroupFunctor k K) →* Gal(L/k) where
  toFun g := g.val (op L)
  map_one' := rfl
  map_mul' _ _ := rfl
/-
**InfiniteGalois.finGaloisGroupFunctor_map_proj_eq_proj** 是 Mathlib 中的一个引理，位于命名空
间 `InfiniteGalois`。
形式化陈述：finGaloisGroupFunctor_map_proj_eq_proj (g : limit (asProfiniteGaloisGroupF
unctor k K)) {L₁ L₂ : FiniteGaloisIntermediateField k K} (h : L₁ ⟶ L₂) : (finGal
oisGroupFunctor k K).map h.op (proj L₂ g) = proj L₁ g
参数：g : limit (asProfiniteGaloisGroupFunctor k K)；h : L₁ ⟶ L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma finGaloisGroupFunctor_map_proj_eq_proj (g : limit (asProfiniteGaloisGroupFunctor k K))
    {L₁ L₂ : FiniteGaloisIntermediateField k K} (h : L₁ ⟶ L₂) :
    (finGaloisGroupFunctor k K).map h.op (proj L₂ g) = proj L₁ g :=
  g.prop h.op
/-
**InfiniteGalois.proj_of_le** 是 Mathlib 中的一个引理，位于命名空间 `InfiniteGalois`。
形式化陈述：proj_of_le (L : FiniteGaloisIntermediateField k K) (g : limit (asProfinite
GaloisGroupFunctor k K)) (x : L) (L' : FiniteGaloisIntermediateField k K) (h : L
 <= L') : (proj L g x).val = (proj L' g ⟨x, h x.2⟩).val
参数：L : FiniteGaloisIntermediateField k K；g : limit (asProfiniteGaloisGroupFuncto
r k K)；x : L；L' : FiniteGaloisIntermediateField k K；h : L <= L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `InfiniteGalois.finGaloisGroupFunctor_map_proj_eq_proj`：finGaloisGroupFun
ctor_map_proj_eq_proj (g : limit (asProfiniteGaloisGroupFunctor k K)) {L₁ L₂ : F
initeGaloisIntermediateField k K} (h : L₁ ⟶…
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
-/
lemma proj_of_le (L : FiniteGaloisIntermediateField k K)
    (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : L)
    (L' : FiniteGaloisIntermediateField k K) (h : L ≤ L') :
    (proj L g x).val = (proj L' g ⟨x, h x.2⟩).val := by
  induction L with | _ L => ?_
  induction L' with | _ L' => ?_
  let : Algebra L L' := RingHom.toAlgebra (Subsemiring.inclusion h)
  let : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← finGaloisGroupFunctor_map_proj_eq_proj g h.hom]
  change (algebraMap L' K (algebraMap L L' (AlgEquiv.restrictNormal (proj (mk L') g) L x))) = _
  rw [AlgEquiv.restrictNormal_commutes (proj (mk L') g) L]
  rfl
/-
**InfiniteGalois.proj_adjoin_singleton_val** 是 Mathlib 中的一个引理，位于命名空间 `InfiniteGa
lois`。
形式化陈述：proj_adjoin_singleton_val [IsGalois k K] (g : limit (asProfiniteGaloisGrou
pFunctor k K)) (x : K) (y : adjoin k {x}) (L : FiniteGaloisIntermediateField k K
) (h : x in L.toIntermediateField) : (proj (adjoin k {x}) g y).val = (proj L g ⟨
y, adjoin_simple_le_iff.mpr h y.2⟩).val
参数：g : limit (asProfiniteGaloisGroupFunctor k K)；x : K；y : adjoin k {x}；L : Fini
teGaloisIntermediateField k K；h : x in L.toIntermediateField。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `InfiniteGalois.proj_of_le`：proj_of_le (L : FiniteGaloisIntermediateField
 k K) (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : L) (L' : FiniteGalois
IntermediateFie…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FiniteGaloisIntermediateField.adjoin_simple_le_iff`：adjoin_simple_le_iff
 [IsGalois k K] {x : K} {L : FiniteGaloisIntermediateField k K} : adjoin k {x} <
= L ↔ x in L.toIntermediateField
-/
lemma proj_adjoin_singleton_val [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
    (x : K) (y : adjoin k {x}) (L : FiniteGaloisIntermediateField k K)
    (h : x ∈ L.toIntermediateField) :
    (proj (adjoin k {x}) g y).val = (proj L g ⟨y, adjoin_simple_le_iff.mpr h y.2⟩).val :=
  proj_of_le _ g y _ _

set_option backward.privateInPublic true in
/-- A function from `K` to `K` defined pointwise using a family of compatible elements of
`Gal(L/k)` where `L` is a `FiniteGaloisIntermediateField` -/
/-
**InfiniteGalois.toAlgEquivAux** 是 Mathlib 中的一个定义，位于命名空间 `InfiniteGalois`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from `K` to `K` defined pointwise using a family of compatible elemen
ts of
`Gal(L/k)` where `L` is a `FiniteGaloisIntermediateField`
-/
private noncomputable def toAlgEquivAux [IsGalois k K]
    (g : limit (asProfiniteGaloisGroupFunctor k K)) : K → K :=
  fun x ↦ (proj (adjoin k {x}) g ⟨x, subset_adjoin _ _ (by simp only [Set.mem_singleton_iff])⟩).val

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**InfiniteGalois.toAlgEquivAux_eq_proj_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Infinit
eGalois`。
形式化陈述：toAlgEquivAux_eq_proj_of_mem [IsGalois k K] (g : limit (asProfiniteGaloisG
roupFunctor k K)) (x : K) (L : FiniteGaloisIntermediateField k K) (hx : x in L.t
oIntermediateField) : toAlgEquivAux g x = (proj L g ⟨x, hx⟩).val
参数：g : limit (asProfiniteGaloisGroupFunctor k K)；x : K；L : FiniteGaloisIntermedi
ateField k K；hx : x in L.toIntermediateField。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `InfiniteGalois.proj_adjoin_singleton_val`：proj_adjoin_singleton_val [IsG
alois k K] (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : K) (y : adjoin k
 {x}) (L : FiniteGaloisInterme…
-/
lemma toAlgEquivAux_eq_proj_of_mem [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
    (x : K) (L : FiniteGaloisIntermediateField k K) (hx : x ∈ L.toIntermediateField) :
    toAlgEquivAux g x = (proj L g ⟨x, hx⟩).val :=
  proj_adjoin_singleton_val g _ _ L hx

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**InfiniteGalois.mk_toAlgEquivAux** 是 Mathlib 中的一个引理，位于命名空间 `InfiniteGalois`。
形式化陈述：mk_toAlgEquivAux [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor 
k K)) (x : K) (L : FiniteGaloisIntermediateField k K) (hx' : toAlgEquivAux g x i
n L.toIntermediateField) (hx : x in L.toIntermediateField) : (⟨toAlgEquivAux g x
, hx'⟩ : L.toIntermediateField) = proj L g ⟨x, hx⟩
参数：g : limit (asProfiniteGaloisGroupFunctor k K)；x : K；L : FiniteGaloisIntermedi
ateField k K；hx' : toAlgEquivAux g x in L.toIntermediateField；hx : x in L.toInte
rmediateField。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用引理 `InfiniteGalois.toAlgEquivAux_eq_proj_of_mem`：toAlgEquivAux_eq_proj_of_me
m [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : K) (L : Fi
niteGaloisIntermediateField k K) …
-/
lemma mk_toAlgEquivAux [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : K)
    (L : FiniteGaloisIntermediateField k K) (hx' : toAlgEquivAux g x ∈ L.toIntermediateField)
    (hx : x ∈ L.toIntermediateField) :
    (⟨toAlgEquivAux g x, hx'⟩ : L.toIntermediateField) = proj L g ⟨x, hx⟩ := by
  rw [Subtype.ext_iff, Subtype.coe_mk, toAlgEquivAux_eq_proj_of_mem]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**InfiniteGalois.toAlgEquivAux_eq_liftNormal** 是 Mathlib 中的一个引理，位于命名空间 `Infinite
Galois`。
形式化陈述：toAlgEquivAux_eq_liftNormal [IsGalois k K] (g : limit (asProfiniteGaloisGr
oupFunctor k K)) (x : K) (L : FiniteGaloisIntermediateField k K) (hx : x in L.to
IntermediateField) : toAlgEquivAux g x = (proj L g).liftNormal K x
参数：g : limit (asProfiniteGaloisGroupFunctor k K)；x : K；L : FiniteGaloisIntermedi
ateField k K；hx : x in L.toIntermediateField。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InfiniteGalois.toAlgEquivAux_eq_proj_of_mem`：toAlgEquivAux_eq_proj_of_me
m [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : K) (L : Fi
niteGaloisIntermediateField k K) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.liftNormal_commutes`：AlgEquiv.liftNormal_commutes [Normal F E] 
(x : K₁) : χ.liftNormal E (algebraMap K₁ E x) = algebraMap K₂ E (χ x)
-/
lemma toAlgEquivAux_eq_liftNormal [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
    (x : K) (L : FiniteGaloisIntermediateField k K) (hx : x ∈ L.toIntermediateField) :
    toAlgEquivAux g x = (proj L g).liftNormal K x := by
  rw [toAlgEquivAux_eq_proj_of_mem g x L hx]
  exact (AlgEquiv.liftNormal_commutes (proj L g) _ ⟨x, hx⟩).symm

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `toAlgEquivAux` as an `AlgEquiv`.
It is done by using above lifting lemmas on bigger `FiniteGaloisIntermediateField`. -/
@[simps]
/-
**InfiniteGalois.limitToAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `InfiniteGalois`。
形式化陈述：limitToAlgEquiv [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k
 K)) : Gal(K/k) where toFun
参数：g : limit (asProfiniteGaloisGroupFunctor k K)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toAlgEquivAux` as an `AlgEquiv`.
It is done by using above lifting lemmas on bigger `FiniteGaloisIntermediateFiel
d`.
-/
noncomputable def limitToAlgEquiv [IsGalois k K]
    (g : limit (asProfiniteGaloisGroupFunctor k K)) : Gal(K/k) where
  toFun := toAlgEquivAux g
  invFun := toAlgEquivAux g⁻¹
  left_inv x := by
    let L := adjoin k {x, toAlgEquivAux g x}
    have hx : x ∈ L.1 := subset_adjoin _ _ (Set.mem_insert x {toAlgEquivAux g x})
    have hx' : toAlgEquivAux g x ∈ L.1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [toAlgEquivAux_eq_proj_of_mem _ _ L hx', map_inv, AlgEquiv.aut_inv,
      mk_toAlgEquivAux g x L hx' hx, AlgEquiv.symm_apply_apply]
  right_inv x := by
    let L := adjoin k {x, toAlgEquivAux g⁻¹ x}
    have hx : x ∈ L.1 := subset_adjoin _ _ (Set.mem_insert x {toAlgEquivAux g⁻¹ x})
    have hx' : toAlgEquivAux g⁻¹ x ∈ L.1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [toAlgEquivAux_eq_proj_of_mem _ _ L hx', mk_toAlgEquivAux g⁻¹ x L hx' hx, map_inv,
      AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  map_mul' x y := by
    have hx : x ∈ (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert x {y})
    have hy : y ∈ (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    rw [toAlgEquivAux_eq_liftNormal g x (adjoin k {x, y}) hx,
      toAlgEquivAux_eq_liftNormal g y (adjoin k {x, y}) hy,
      toAlgEquivAux_eq_liftNormal g (x * y) (adjoin k {x, y}) (mul_mem hx hy), map_mul]
  map_add' x y := by
    have hx : x ∈ (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert x {y})
    have hy : y ∈ (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [toAlgEquivAux_eq_liftNormal g x (adjoin k {x, y}) hx,
      toAlgEquivAux_eq_liftNormal g y (adjoin k {x, y}) hy,
      toAlgEquivAux_eq_liftNormal g (x + y) (adjoin k {x, y}) (add_mem hx hy), map_add]
  commutes' x := by
    simp only [toAlgEquivAux_eq_liftNormal g _ ⊥ (algebraMap_mem _ x), AlgEquiv.commutes]

variable (k K) in
/-- `algEquivToLimit` as a `MulEquiv`. -/
/-
**InfiniteGalois.mulEquivToLimit** 是 Mathlib 中的一个定义，位于命名空间 `InfiniteGalois`。
形式化陈述：mulEquivToLimit [IsGalois k K] : Gal(K/k) ≃* limit (asProfiniteGaloisGroup
Functor k K) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`algEquivToLimit` as a `MulEquiv`.
-/
noncomputable def mulEquivToLimit [IsGalois k K] :
    Gal(K/k) ≃* limit (asProfiniteGaloisGroupFunctor k K) where
  toFun := algEquivToLimit k K
  map_mul' := map_mul _
  invFun := limitToAlgEquiv
  left_inv := fun f ↦ AlgEquiv.ext fun x ↦
    AlgEquiv.restrictNormal_commutes f (adjoin k {x}).1 ⟨x, _⟩
  right_inv := fun g ↦ by
    apply Subtype.val_injective
    ext L
    change (limitToAlgEquiv g).restrictNormal _ = _
    ext x
    have : ((limitToAlgEquiv g).restrictNormal L.unop) x = (limitToAlgEquiv g) x.1 := by
      exact AlgEquiv.restrictNormal_commutes (limitToAlgEquiv g) L.unop x
    simp_rw [this]
    exact proj_adjoin_singleton_val _ _ _ _ x.2

open scoped Topology in
/-
**InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois** 是 Mathlib 中的一个引理，位
于命名空间 `InfiniteGalois`。
形式化陈述：krullTopology_mem_nhds_one_iff_of_isGalois [IsGalois k K] (A : Set Gal(K/k
)) : A in 𝓝 1 ↔ exists (L : FiniteGaloisIntermediateField k K), (L.fixingSubgrou
p : Set _) subseteq A
参数：A : Set Gal(K/k)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `krullTopology_mem_nhds_one_iff_of_normal`：krullTopology_mem_nhds_one_iff
_of_normal (K L : Type*) [Field K] [Field L] [Algebra K L] [Normal K L] (s : Set
 Gal(L/K)) : s in 𝓝 1 ↔ exists…
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用定理 `FiniteGaloisIntermediateField.instFiniteDimensionalSubtypeMemIntermediat
eField`：∀ (k : Type u_1) (K : Type u_2) [inst : Field k] [inst_1 : Field K] [ins
t_2 : Algebra k K]   (L : FiniteGaloisIntermediateField k K), Finite…
· 使用定理 `FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateField`：∀
 (k : Type u_1) (K : Type u_2) [inst : Field k] [inst_1 : Field K] [inst_2 : Alg
ebra k K]   (L : FiniteGaloisIntermediateField k K), IsGalo…
-/
lemma krullTopology_mem_nhds_one_iff_of_isGalois [IsGalois k K] (A : Set Gal(K/k)) :
    A ∈ 𝓝 1 ↔ ∃ (L : FiniteGaloisIntermediateField k K), (L.fixingSubgroup : Set _) ⊆ A := by
  rw [krullTopology_mem_nhds_one_iff_of_normal]
  exact ⟨fun ⟨L, _, hL, hsub⟩ ↦ ⟨{ toIntermediateField := L, isGalois := ⟨⟩ }, hsub⟩,
    fun ⟨L, hL⟩ ↦ ⟨L, inferInstance, inferInstance, hL⟩⟩
/-
**InfiniteGalois.isOpen_mulEquivToLimit_image_fixingSubgroup** 是 Mathlib 中的一个引理，
位于命名空间 `InfiniteGalois`。
形式化陈述：isOpen_mulEquivToLimit_image_fixingSubgroup [IsGalois k K] (L : FiniteGalo
isIntermediateField k K) : IsOpen (mulEquivToLimit k K '' L.fixingSubgroup)
参数：L : FiniteGaloisIntermediateField k K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateField`：∀
 (k : Type u_1) (K : Type u_2) [inst : Field k] [inst_1 : Field K] [inst_2 : Alg
ebra k K]   (L : FiniteGaloisIntermediateField k K), IsGalo…
· 使用定理 `FiniteGaloisIntermediateField.mem_fixingSubgroup_iff`：∀ {k : Type u_1} {
K : Type u_2} [inst : Field k] [inst_1 : Field K] [inst_2 : Algebra k K] (α : Ga
l(K/k))   (L : FiniteGaloisIntermediateFie…
· 使用定理 `isOpen_induced`：isOpen_induced {s : Set β} (h : IsOpen s) : IsOpen[induc
ed f t] (f ⁻¹' s)
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `trivial`：True
-/
lemma isOpen_mulEquivToLimit_image_fixingSubgroup [IsGalois k K]
    (L : FiniteGaloisIntermediateField k K) : IsOpen (mulEquivToLimit k K '' L.fixingSubgroup) := by
  let fix1 : Set (Π L, (asProfiniteGaloisGroupFunctor k K).obj L) := {f | f (op L) = 1}
  suffices mulEquivToLimit k K '' L.1.fixingSubgroup = Set.preimage Subtype.val fix1 by
    rw [this]
    exact (isOpen_induced <| (continuous_apply (op L)).isOpen_preimage {1} trivial)
  ext x
  obtain ⟨σ, rfl⟩ := (mulEquivToLimit k K).surjective x
  simpa using! FiniteGaloisIntermediateField.mem_fixingSubgroup_iff σ L
/-
**InfiniteGalois.mulEquivToLimit_symm_continuous** 是 Mathlib 中的一个引理，位于命名空间 `Infi
niteGalois`。
形式化陈述：mulEquivToLimit_symm_continuous [IsGalois k K] : Continuous (mulEquivToLim
it k K).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_continuousAt_one`：continuous_of_continuousAt_one {M hom : 
Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] [FunLike hom G M] 
[MonoidHomClass hom …
· 使用定理 `Subgroup.instIsTopologicalGroupSubtypeMem`：∀ {G : Type w} [inst : Topolo
gicalSpace G] [inst_1 : Group G] [IsTopologicalGroup G] (S : Subgroup G),   IsTo
pologicalGroup ↥S
· 使用定理 `ProfiniteGrp.topologicalGroup`：∀ (self : ProfiniteGrp.{u}), IsTopologica
lGroup ↑self.toProfinite.toTop
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `instIsTopologicalGroupAlgEquiv`：∀ (K : Type u_1) (L : Type u_2) [inst : 
Field K] [inst_1 : Field L] [inst_2 : Algebra K L], IsTopologicalGroup Gal(L/K)
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousAt_def`：continuousAt_def : ContinuousAt f x ↔ forall A in 𝓝 (f
 x), f ⁻¹' A in 𝓝 x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `InfiniteGalois.isOpen_mulEquivToLimit_image_fixingSubgroup`：isOpen_mulEq
uivToLimit_image_fixingSubgroup [IsGalois k K] (L : FiniteGaloisIntermediateFiel
d k K) : IsOpen (mulEquivToLimit k K '' L.fixing…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
（共 33 条，此处仅展示前 30 条）
-/
lemma mulEquivToLimit_symm_continuous [IsGalois k K] : Continuous (mulEquivToLimit k K).symm := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  simp only [map_one, krullTopology_mem_nhds_one_iff_of_isGalois, ← MulEquiv.coe_toEquiv_symm,
    ← MulEquiv.toEquiv_eq_coe, ← (mulEquivToLimit k K).image_eq_preimage_symm]
  intro H ⟨L, le⟩
  rw [mem_nhds_iff]
  use mulEquivToLimit k K '' L.1.fixingSubgroup
  simp only [isOpen_mulEquivToLimit_image_fixingSubgroup L]
  simpa [one_mem] using Set.image_subset_iff.mp (Set.image_mono le)

variable (k K)

/-- The `ContinuousMulEquiv` between `Gal(K/k)` and `lim Gal(L/k)` where `L` is a
  `FiniteGaloisIntermediateField` ordered by inverse inclusion, obtained
  from `InfiniteGalois.mulEquivToLimit` -/
/-
**InfiniteGalois.continuousMulEquivToLimit** 是 Mathlib 中的一个定义，位于命名空间 `InfiniteGa
lois`。
形式化陈述：continuousMulEquivToLimit [IsGalois k K] : Gal(K/k) ≃ₜ* limit (asProfinite
GaloisGroupFunctor k K) where toMulEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `InfiniteGalois.algEquivToLimit_continuous`：algEquivToLimit_continuous : 
Continuous (algEquivToLimit k K)
· 使用引理 `InfiniteGalois.mulEquivToLimit_symm_continuous`：mulEquivToLimit_symm_con
tinuous [IsGalois k K] : Continuous (mulEquivToLimit k K).symm

--- 原说明 ---
The `ContinuousMulEquiv` between `Gal(K/k)` and `lim Gal(L/k)` where `L` is a
  `FiniteGaloisIntermediateField` ordered by inverse inclusion, obtained
  from `InfiniteGalois.mulEquivToLimit`
-/
noncomputable def continuousMulEquivToLimit [IsGalois k K] :
    Gal(K/k) ≃ₜ* limit (asProfiniteGaloisGroupFunctor k K) where
  toMulEquiv := mulEquivToLimit k K
  continuous_toFun := algEquivToLimit_continuous
  continuous_invFun := mulEquivToLimit_symm_continuous
/-
**InfiniteGalois.** 是 Mathlib 中的一个实例，位于命名空间 `InfiniteGalois`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsGalois k K] : CompactSpace Gal(K/k) :=
  (continuousMulEquivToLimit k K).symm.compactSpace

/-- `Gal(K/k)` as a profinite group as there is
a `ContinuousMulEquiv` to a `ProfiniteGrp` given above -/
/-
**InfiniteGalois.profiniteGalGrp** 是 Mathlib 中的一个定义，位于命名空间 `InfiniteGalois`。
形式化陈述：profiniteGalGrp [IsGalois k K] : ProfiniteGrp
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalGroupAlgEquiv`：∀ (K : Type u_1) (L : Type u_2) [inst : 
Field K] [inst_1 : Field L] [inst_2 : Algebra K L], IsTopologicalGroup Gal(L/K)
· 使用定理 `InfiniteGalois.instCompactSpaceAlgEquivOfIsGalois`：∀ (k : Type u_3) (K :
 Type u_4) [inst : Field k] [inst_1 : Field K] [inst_2 : Algebra k K] [IsGalois 
k K],   CompactSpace Gal(K/k)

--- 原说明 ---
`Gal(K/k)` as a profinite group as there is
a `ContinuousMulEquiv` to a `ProfiniteGrp` given above
-/
noncomputable def profiniteGalGrp [IsGalois k K] : ProfiniteGrp :=
  ProfiniteGrp.of Gal(K/k)

/-- The categorical isomorphism between `profiniteGalGrp` and `lim Gal(L/k)` where `L` is a
  `FiniteGaloisIntermediateField` ordered by inverse inclusion -/
/-
**InfiniteGalois.profiniteGalGrpIsoLimit** 是 Mathlib 中的一个定义，位于命名空间 `InfiniteGalo
is`。
形式化陈述：profiniteGalGrpIsoLimit [IsGalois k K] : profiniteGalGrp k K ≅ limit (asPr
ofiniteGaloisGroupFunctor k K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical isomorphism between `profiniteGalGrp` and `lim Gal(L/k)` where `
L` is a
  `FiniteGaloisIntermediateField` ordered by inverse inclusion
-/
noncomputable def profiniteGalGrpIsoLimit [IsGalois k K] :
    profiniteGalGrp k K ≅ limit (asProfiniteGaloisGroupFunctor k K) :=
  ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivToLimit k K)

end InfiniteGalois

end Profinite

