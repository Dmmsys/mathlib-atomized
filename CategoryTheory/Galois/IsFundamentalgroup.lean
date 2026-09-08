/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!

# Universal property of fundamental group

Let `C` be a Galois category with fiber functor `F`. While in informal mathematics, we tend to
identify known groups from other contexts (e.g. the absolute Galois group of a field) with
the automorphism group `Aut F` of certain fiber functors `F`, this causes friction in formalization.

Hence, in this file we develop conditions when a topological group `G` is canonically isomorphic to
the automorphism group `Aut F` of `F`. Consequently, the API for Galois categories and their fiber
functors should be stated in terms of an abstract topological group `G` satisfying
`IsFundamentalGroup` in the places where `Aut F` would appear.

## Main definition

Given a compact, topological group `G` with an action on `F.obj X` on each `X`, we say that
`G` is a fundamental group of `F` (`IsFundamentalGroup F G`), if

- `naturality`: the `G`-action on `F.obj X` is compatible with morphisms in `C`
- `transitive_of_isGalois`: `G` acts transitively on `F.obj X` for all Galois objects `X : C`
- `continuous_smul`: the action of `G` on `F.obj X` is continuous if `F.obj X` is equipped with the
  discrete topology for all `X : C`.
- `non_trivial'`: if `g : G` acts trivially on all `F.obj X`, then `g = 1`.

Given this data, we define `toAut F G : G →* Aut F` in the natural way.

## Main results

- `toAut_bijective`: `toAut F G` is a group isomorphism given `IsFundamentalGroup F G`.
- `toAut_isHomeomorph`: `toAut F G` is a homeomorphism given `IsFundamentalGroup F G`.

## TODO

- Develop further equivalent conditions, in particular, relate the condition `non_trivial` with
  `G` being a `T2Space`.

-/

@[expose] public section

universe u₁ u₂ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

section

variable (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)]

/-- We say `G` acts naturally on the fibers of `F` if for every `f : X ⟶ Y`, the `G`-actions
on `F.obj X` and `F.obj Y` are compatible with `F.map f`. -/
/-
**CategoryTheory.PreGaloisCategory.IsNaturalSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ca
tegoryTheory.PreGaloisCategory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{u₂, u₁} C] →     (F : C
ategoryTheory.Functor C FintypeCat) →       (G : Type u_1) → [inst_1 : Group G] 
→ [(X : C) → MulAction G (F.obj X).obj] → Prop
参数：F : CategoryTheory.Functor C FintypeCat；G : Type u_1；X : C；F.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say `G` acts naturally on the fibers of `F` if for every `f : X ⟶ Y`, the `G`
-actions
on `F.obj X` and `F.obj Y` are compatible with `F.map f`.
-/
class IsNaturalSMul : Prop where
  naturality (g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X) : F.map f (g • x) = g • F.map f x

set_option backward.privateInPublic true in
variable {G} in
@[simps! -isSimp]
/-
**CategoryTheory.PreGaloisCategory.isoOnObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def isoOnObj (g : G) (X : C) : F.obj X ≅ F.obj X :=
  FintypeCat.equivEquivIso <| {
    toFun := fun x ↦ g • x
    invFun := fun x ↦ g⁻¹ • x
    left_inv := fun _ ↦ by simp
    right_inv := fun _ ↦ by simp
  }

variable [IsNaturalSMul F G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `G` acts naturally on `F.obj X` for each `X : C`, this is the canonical
group homomorphism into the automorphism group of `F`. -/
/-
**CategoryTheory.PreGaloisCategory.toAut** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.PreGaloisCategory`。
形式化陈述：toAut : G ->* Aut F where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` acts naturally on `F.obj X` for each `X : C`, this is the canonical
group homomorphism into the automorphism group of `F`.
-/
def toAut : G →* Aut F where
  toFun g := NatIso.ofComponents (isoOnObj F g) <| by
    intro X Y f
    ext
    exact (IsNaturalSMul.naturality _ _ _).symm
  map_one' := by
    ext
    dsimp [isoOnObj]
    cat_disch
  map_mul' := by
    intro g h
    ext X x
    apply mul_smul

variable {G} in
@[simp]
/-
**CategoryTheory.PreGaloisCategory.toAut_hom_app_apply** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.PreGaloisCategory`。
形式化陈述：toAut_hom_app_apply (g : G) {X : C} (x : F.obj X) : (toAut F G g).hom.app 
X x = g • x
参数：g : G；x : F.obj X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAut_hom_app_apply (g : G) {X : C} (x : F.obj X) : (toAut F G g).hom.app X x = g • x :=
  rfl

/-- `toAut` is injective, if only the identity acts trivially on every fiber. -/
/-
**CategoryTheory.PreGaloisCategory.toAut_injective_of_non_trivial** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：toAut_injective_of_non_trivial (h : forall (g : G), (forall (X : C) (x : F
.obj X), g • x = x) -> g = 1) : Function.Injective (toAut F G)
参数：h : forall (g : G), (forall (X : C) (x : F.obj X), g • x = x) -> g = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_hom_app_apply`：toAut_hom_app_appl
y (g : G) {X : C} (x : F.obj X) : (toAut F G g).hom.app X x = g • x
· 使用定理 `FintypeCat.id_apply`：id_apply (X : FintypeCat) (x : X) : (𝟙 X : X -> X) 
x = x

--- 原说明 ---
`toAut` is injective, if only the identity acts trivially on every fiber.
-/
lemma toAut_injective_of_non_trivial (h : ∀ (g : G), (∀ (X : C) (x : F.obj X), g • x = x) → g = 1) :
    Function.Injective (toAut F G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g (hg : toAut F G g = 1)
  refine h g (fun X x ↦ ?_)
  have : (toAut F G g).hom.app X = 𝟙 (F.obj X) := by
    rw [hg]
    rfl
  rw [← toAut_hom_app_apply, this, FintypeCat.id_apply]

variable [GaloisCategory C] [FiberFunctor F]
/-
**CategoryTheory.PreGaloisCategory.toAut_continuous** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.PreGaloisCategory`。
形式化陈述：toAut_continuous [TopologicalSpace G] [IsTopologicalGroup G] [forall (X : 
C), ContinuousSMul G (F.obj X)] : Continuous (toAut F G)
参数：X : C；F.obj X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `continuous_of_continuousAt_one`：continuous_of_continuousAt_one {M hom : 
Type*} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] [FunLike hom G M] 
[MonoidHomClass hom …
· 使用定理 `CategoryTheory.PreGaloisCategory.instContinuousMulAutFunctorFintypeCat`：
∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTheory.
Functor C FintypeCat),   ContinuousMul (CategoryTheory.Aut F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousAt_def`：continuousAt_def : ContinuousAt f x ↔ forall A in 𝓝 (f
 x), f ⁻¹' A in 𝓝 x
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff'`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (t : Set α), t ∈ l ↔ ∃ i, 
p i ∧ s i ⊆ t
· 使用引理 `CategoryTheory.PreGaloisCategory.nhds_one_has_basis_stabilizers`：nhds_on
e_has_basis_stabilizers : (nhds (1 : Aut F)).HasBasis (fun _ => True) (fun X : P
ointedGaloisObject F => MulAction.stabilizer (Aut F) …
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用引理 `stabilizer_isOpen`：stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOp
en (MulAction.stabilizer M x : Set M)
· 使用引理 `CategoryTheory.PreGaloisCategory.obj_discreteTopology`：obj_discreteTopol
ogy (X : C) : DiscreteTopology (F.obj X)
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
lemma toAut_continuous [TopologicalSpace G] [IsTopologicalGroup G]
    [∀ (X : C), ContinuousSMul G (F.obj X)] :
    Continuous (toAut F G) := by
  apply continuous_of_continuousAt_one
  rw [continuousAt_def, map_one]
  intro A hA
  obtain ⟨X, _, hX⟩ := ((nhds_one_has_basis_stabilizers F).mem_iff' A).mp hA
  rw [mem_nhds_iff]
  exact ⟨MulAction.stabilizer G X.pt, Set.preimage_mono (f := toAut F G) hX,
    stabilizer_isOpen G X.pt, one_mem _⟩

variable {G}

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.PreGaloisCategory.action_ext_of_isGalois** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：action_ext_of_isGalois {t : F ⟶ F} {X : C} [IsGalois X] {g : G} (x : F.obj
 X) (hg : g • x = t.app X x) (y : F.obj X) : g • y = t.app X y
参数：x : F.obj X；hg : g • x = t.app X x；y : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback`：
injective_of_mono_of_preservesPullback {X Y : C} (f : X ⟶ Y) [Mono f] [Preserves
LimitsOfShape WalkingCospan (forget C)] : Function.Injective…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesPullbacks`：∀ {C :
 Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.P
reGaloisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.FintypeCat.instPreservesFiniteLimitsFintypeCatForg
etFunObjFinite`：CategoryTheory.Limits.PreservesFiniteLimits (CategoryTheory.forg
et FintypeCat)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.PreGaloisCategory.IsNaturalSMul.naturality`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryTheory.Functor C Fin
typeCat} {G : Type u_1}   {inst_1 : Group G} {i…
· 使用引理 `FunctorToFintypeCat.naturality`：naturality (σ : F ⟶ G) (f : X ⟶ Y) (x : 
F.obj X) : σ.app Y (F.map f x) = G.map f (σ.app X x)
-/
lemma action_ext_of_isGalois {t : F ⟶ F} {X : C} [IsGalois X] {g : G} (x : F.obj X)
    (hg : g • x = t.app X x) (y : F.obj X) : g • y = t.app X y := by
  obtain ⟨φ, (rfl : F.map φ.hom y = x)⟩ := MulAction.exists_smul_eq (Aut X) y x
  have : Function.Injective (F.map φ.hom) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map φ.hom)
  apply this
  rw [IsNaturalSMul.naturality, hg, FunctorToFintypeCat.naturality]

variable (G)
/-
**CategoryTheory.PreGaloisCategory.toAut_surjective_isGalois** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：toAut_surjective_isGalois (t : Aut F) (X : C) [IsGalois X] [MulAction.IsPr
etransitive G (F.obj X)] : exists (g : G), forall (x : F.obj X), g • x = t.hom.a
pp X x
参数：t : Aut F；X : C；F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.toIsConnected`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.GaloisCate
gory C} {X : C}   [self : CategoryTheory.PreG…
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用引理 `CategoryTheory.PreGaloisCategory.action_ext_of_isGalois`：action_ext_of_i
sGalois {t : F ⟶ F} {X : C} [IsGalois X] {g : G} (x : F.obj X) (hg : g • x = t.a
pp X x) (y : F.obj X) : g • y = t.app X y
-/
lemma toAut_surjective_isGalois (t : Aut F) (X : C) [IsGalois X]
    [MulAction.IsPretransitive G (F.obj X)] :
    ∃ (g : G), ∀ (x : F.obj X), g • x = t.hom.app X x := by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F X
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a (t.hom.app X a)
  exact ⟨g, action_ext_of_isGalois F _ hg⟩
/-
**CategoryTheory.PreGaloisCategory.toAut_surjective_isGalois_finite_family** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：toAut_surjective_isGalois_finite_family (t : Aut F) {ι : Type*} [Finite ι]
 (X : ι -> C) [forall i, IsGalois (X i)] (h : forall (X : C) [IsGalois X], MulAc
tion.IsPretransitive G (F.obj X)) : exists (g : G), forall (i : ι) (x : F.obj (X
 i)), g • x = t.hom.app (X i) x
参数：t : Aut F；X : ι -> C；X i；h : forall (X : C) [IsGalois X], MulAction.IsPretran
sitive G (F.obj X)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.toIsConnected`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.GaloisCate
gory C} {X : C}   [self : CategoryTheory.PreG…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `CategoryTheory.PreGaloisCategory.instHasFiniteLimits`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.PreGaloisCategory C], 
  CategoryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteProductsOfPreservesFiniteLimits
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.instPreservesFiniteLimitsF
intypeCat`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] {F : Cate
goryTheory.Functor C FintypeCat}   [inst_1 : CategoryTheory.PreGaloisCa…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FintypeCat.inv_hom_id_apply`：inv_hom_id_apply {X Y : FintypeCat} (f : X 
≅ Y) (y : Y) : f.hom (f.inv y) = y
· 使用引理 `CategoryTheory.Limits.FintypeCat.productEquiv_symm_comp_π_apply`：product
Equiv_symm_comp_π_apply {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u}) (x : fo
rall i, X i) (i : ι) : Pi.π X i ((productEquiv X).sym…
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_fiber`：exists
_hom_from_galois_of_fiber (X : C) (x : F.obj X) : exists (A : C) (f : A ⟶ X) (a 
: F.obj A), IsGalois A ∧ F.map f a = x
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_surjective_isGalois`：toAut_surjec
tive_isGalois (t : Aut F) (X : C) [IsGalois X] [MulAction.IsPretransitive G (F.o
bj X)] : exists (g : G), forall (x : F.obj X), g…
· 使用引理 `CategoryTheory.PreGaloisCategory.action_ext_of_isGalois`：action_ext_of_i
sGalois {t : F ⟶ F} {X : C} [IsGalois X] {g : G} (x : F.obj X) (hg : g • x = t.a
pp X x) (y : F.obj X) : g • y = t.app X y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.PreGaloisCategory.IsNaturalSMul.naturality`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryTheory.Functor C Fin
typeCat} {G : Type u_1}   {inst_1 : Group G} {i…
· 使用引理 `FunctorToFintypeCat.naturality`：naturality (σ : F ⟶ G) (f : X ⟶ Y) (x : 
F.obj X) : σ.app Y (F.map f x) = G.map f (σ.app X x)
-/
lemma toAut_surjective_isGalois_finite_family (t : Aut F) {ι : Type*} [Finite ι] (X : ι → C)
    [∀ i, IsGalois (X i)] (h : ∀ (X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)) :
    ∃ (g : G), ∀ (i : ι) (x : F.obj (X i)), g • x = t.hom.app (X i) x := by
  let x (i : ι) : F.obj (X i) := (nonempty_fiber_of_isConnected F (X i)).some
  let P : C := ∏ᶜ X
  let is₁ : F.obj P ≅ ∏ᶜ fun i ↦ (F.obj (X i)) := PreservesProduct.iso F X
  let is₂ : (∏ᶜ fun i ↦ F.obj (X i) : FintypeCat) ≃ ∀ i, F.obj (X i) :=
    Limits.FintypeCat.productEquiv (fun i ↦ (F.obj (X i)))
  let px : F.obj P := is₁.inv (is₂.symm x)
  have hpx (i : ι) : F.map (Pi.π X i) px = x i := by
    simp only [px, is₁, is₂, ← piComparison_comp_π, ← PreservesProduct.iso_hom,
      FintypeCat.comp_apply]
    rw [FintypeCat.inv_hom_id_apply, FintypeCat.productEquiv_symm_comp_π_apply]
  obtain ⟨A, f, a, _, hfa⟩ := exists_hom_from_galois_of_fiber F P px
  obtain ⟨g, hg⟩ := toAut_surjective_isGalois F G t A
  refine ⟨g, fun i y ↦ action_ext_of_isGalois F (x i) ?_ _⟩
  rw [← hpx i, ← IsNaturalSMul.naturality, FunctorToFintypeCat.naturality,
    ← hfa, FunctorToFintypeCat.naturality, ← IsNaturalSMul.naturality, hg]

open scoped Pointwise

/-- If `G` is a compact, topological group that acts continuously and naturally on the
fibers of `F`, `toAut F G` is surjective if and only if it acts transitively on the fibers
of all Galois objects. This is the `if` direction. For the `only if` see
`isPretransitive_of_surjective`. -/
/-
**CategoryTheory.PreGaloisCategory.toAut_surjective_of_isPretransitive** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：toAut_surjective_of_isPretransitive [TopologicalSpace G] [IsTopologicalGro
up G] [CompactSpace G] [forall (X : C), ContinuousSMul G (F.obj X)] (h : forall 
(X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)) : Function.Surjecti
ve (toAut F G)
参数：X : C；F.obj X；h : forall (X : C) [IsGalois X], MulAction.IsPretransitive G (F
.obj X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `IsCompact.inter_iInter_nonempty`：IsCompact.inter_iInter_nonempty {ι : Ty
pe v} (hs : IsCompact s) (t : ι -> Set X) (htc : forall i, IsClosed (t i)) (hst 
: forall u : Finset ι…
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
· 使用定理 `IsClosed.leftCoset`：IsClosed.leftCoset {U : Set G} (h : IsClosed U) (x :
 G) : IsClosed (x • U)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用引理 `Subgroup.isClosed_of_isOpen`：isClosed_of_isOpen [SeparatelyContinuousMul
 G] (U : Subgroup G) (h : IsOpen (U : Set G)) : IsClosed (U : Set G)
· 使用引理 `stabilizer_isOpen`：stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOp
en (MulAction.stabilizer M x : Set M)
· 使用引理 `CategoryTheory.PreGaloisCategory.obj_discreteTopology`：obj_discreteTopol
ogy (X : C) : DiscreteTopology (F.obj X)
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_surjective_isGalois_finite_family
`：toAut_surjective_isGalois_finite_family (t : Aut F) {ι : Type*} [Finite ι] (X 
: ι -> C) [forall i, IsGalois (X i)] (h : forall (X : C) [IsGa…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.PreGaloisCategory.PointedGaloisObject.isGalois`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] [inst_1 : CategoryTheory.Galo
isCategory C]   {F : CategoryTheory.Functor C Finty…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mem_leftCoset_iff`：mem_leftCoset_iff (a : α) : x in a • s ↔ a⁻¹ * x in s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.PreGaloisCategory.natTrans_ext_of_isGalois`：natTrans_ext_
of_isGalois {G : C ⥤ FintypeCat.{w}} {t s : F ⟶ G} (h : forall (X : C) [IsGalois
 X], t.app X = s.app X) : t = s
· 使用引理 `FintypeCat.hom_ext`：hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall
 x, f x = g x) : f = g
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_surjective_isGalois`：toAut_surjec
tive_isGalois (t : Aut F) (X : C) [IsGalois X] [MulAction.IsPretransitive G (F.o
bj X)] : exists (g : G), forall (x : F.obj X), g…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `G` is a compact, topological group that acts continuously and naturally on t
he
fibers of `F`, `toAut F G` is surjective if and only if it acts transitively on 
the fibers
of all Galois objects. This is the `if` direction. For the `only if` see
`isPretransitive_of_surjective`.
-/
lemma toAut_surjective_of_isPretransitive [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [∀ (X : C), ContinuousSMul G (F.obj X)]
    (h : ∀ (X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)) :
    Function.Surjective (toAut F G) := by
  intro t
  choose gi hgi using (fun X : PointedGaloisObject F ↦ toAut_surjective_isGalois F G t X)
  let cl (X : PointedGaloisObject F) : Set G := gi X • MulAction.stabilizer G X.pt
  let c : Set G := ⋂ i, cl i
  have hne : c.Nonempty := by
    rw [← Set.univ_inter c]
    apply CompactSpace.isCompact_univ.inter_iInter_nonempty
    · intro X
      apply IsClosed.leftCoset
      exact Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen G X.pt)
    · intro s
      rw [Set.univ_inter]
      obtain ⟨gs, hgs⟩ :=
        toAut_surjective_isGalois_finite_family F G t (fun X : s ↦ X.val.obj) h
      use gs
      simp only [Set.mem_iInter]
      intro X hXmem
      rw [mem_leftCoset_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul,
        hgs ⟨X, hXmem⟩, ← hgi X, inv_smul_smul]
  obtain ⟨g, hg⟩ := hne
  refine ⟨g, Iso.ext <| natTrans_ext_of_isGalois _ <| fun X _ ↦ ?_⟩
  ext x
  simp only [toAut_hom_app_apply]
  have : g ∈ (gi ⟨X, x, inferInstance⟩ • MulAction.stabilizer G x : Set G) := by
    simp only [Set.mem_iInter, c] at hg
    exact hg _
  obtain ⟨s, (hsmem : s • x = x), (rfl : gi ⟨X, x, inferInstance⟩ • s = _)⟩ := this
  rw [smul_eq_mul, mul_smul, hsmem]
  exact hgi ⟨X, x, inferInstance⟩ x

/-- If `toAut F G` is surjective, then `G` acts transitively on the fibers of connected objects.
For a converse see `toAut_surjective`. -/
/-
**CategoryTheory.PreGaloisCategory.isPretransitive_of_surjective** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：isPretransitive_of_surjective (h : Function.Surjective (toAut F G)) (X : C
) [IsConnected X] : MulAction.IsPretransitive G (F.obj X) where exists_smul_eq x
 y
参数：h : Function.Surjective (toAut F G)；X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConne
cted`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] [inst_1 : Cate
goryTheory.GaloisCategory C]   (F : CategoryTheory.Functor C Finty…

--- 原说明 ---
If `toAut F G` is surjective, then `G` acts transitively on the fibers of connec
ted objects.
For a converse see `toAut_surjective`.
-/
lemma isPretransitive_of_surjective (h : Function.Surjective (toAut F G)) (X : C)
    [IsConnected X] : MulAction.IsPretransitive G (F.obj X) where
  exists_smul_eq x y := by
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (Aut F) x y
    obtain ⟨g, rfl⟩ := h t
    exact ⟨g, ht⟩

end

section

variable [GaloisCategory C]
variable (G : Type*) [Group G] [∀ (X : C), MulAction G (F.obj X)]

/-- A compact, topological group `G` with a natural action on `F.obj X` for each `X : C`
is a fundamental group of `F`, if `G` acts transitively on the fibers of Galois objects,
the action on `F.obj X` is continuous for all `X : C` and the only trivially acting element of `G`
is the identity. -/
/-
**CategoryTheory.PreGaloisCategory.IsFundamentalGroup** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{u₂, u₁} C] →     (F : C
ategoryTheory.Functor C FintypeCat) →       [CategoryTheory.GaloisCategory C] → 
        (G : Type u_1) →           [inst_2 : Group G] →             [(X : C) → M
ulAction G (F.obj X).obj] →               [inst : TopologicalSpace G] → [IsTopol
ogicalGroup G] → [CompactSpace G] → Prop
参数：F : CategoryTheory.Functor C FintypeCat；G : Type u_1；X : C；F.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compact, topological group `G` with a natural action on `F.obj X` for each `X 
: C`
is a fundamental group of `F`, if `G` acts transitively on the fibers of Galois 
objects,
the action on `F.obj X` is continuous for all `X : C` and the only trivially act
ing element of `G`
is the identity.
-/
class IsFundamentalGroup [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] : Prop
    extends IsNaturalSMul F G where
  transitive_of_isGalois (X : C) [IsGalois X] : MulAction.IsPretransitive G (F.obj X)
  continuous_smul (X : C) : ContinuousSMul G (F.obj X)
  non_trivial' (g : G) : (∀ (X : C) (x : F.obj X), g • x = x) → g = 1

namespace IsFundamentalGroup

attribute [instance] continuous_smul transitive_of_isGalois

variable {G} [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup F G]

/-
**CategoryTheory.PreGaloisCategory.IsFundamentalGroup.non_trivial** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory.IsFundamentalGroup`。
形式化陈述：non_trivial (g : G) (h : forall (X : C) (x : F.obj X), g • x = x) : g = 1
参数：g : G；h : forall (X : C) (x : F.obj X), g • x = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.PreGaloisCategory.IsFundamentalGroup.non_trivial'`：∀ {C :
 Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryTheory.Functo
r C FintypeCat}   {inst_1 : CategoryTheory.GaloisCateg…
-/
lemma non_trivial (g : G) (h : ∀ (X : C) (x : F.obj X), g • x = x) : g = 1 :=
  IsFundamentalGroup.non_trivial' g h

end IsFundamentalGroup

variable [FiberFunctor F]

/-- `Aut F` is a fundamental group for `F`. -/
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Aut F` is a fundamental group for `F`.
-/
instance : IsFundamentalGroup F (Aut F) where
  naturality g _ _ f x := (FunctorToFintypeCat.naturality F F g.hom f x).symm
  transitive_of_isGalois X := FiberFunctor.isPretransitive_of_isConnected F X
  continuous_smul X := continuousSMul_aut_fiber F X
  non_trivial' g h := by
    ext X x
    exact h X x

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup F G]
/-
**CategoryTheory.PreGaloisCategory.toAut_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.PreGaloisCategory`。
形式化陈述：toAut_bijective : Function.Bijective (toAut F G) where left
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.IsFundamentalGroup.toIsNaturalSMul`：∀ {
C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryTheory.Fun
ctor C FintypeCat}   {inst_1 : CategoryTheory.GaloisCateg…
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_injective_of_non_trivial`：toAut_i
njective_of_non_trivial (h : forall (g : G), (forall (X : C) (x : F.obj X), g • 
x = x) -> g = 1) : Function.Injective (toAut F G)
· 使用定理 `CategoryTheory.PreGaloisCategory.IsFundamentalGroup.non_trivial'`：∀ {C :
 Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryTheory.Functo
r C FintypeCat}   {inst_1 : CategoryTheory.GaloisCateg…
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_surjective_of_isPretransitive`：to
Aut_surjective_of_isPretransitive [TopologicalSpace G] [IsTopologicalGroup G] [C
ompactSpace G] [forall (X : C), ContinuousSMul G (F.obj X)…
· 使用定理 `CategoryTheory.PreGaloisCategory.IsFundamentalGroup.continuous_smul`：∀ {
C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryTheory.Fun
ctor C FintypeCat}   {inst_1 : CategoryTheory.GaloisCateg…
· 使用定理 `CategoryTheory.PreGaloisCategory.IsFundamentalGroup.transitive_of_isGalo
is`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryThe
ory.Functor C FintypeCat}   {inst_1 : CategoryTheory.GaloisCateg…
-/
lemma toAut_bijective : Function.Bijective (toAut F G) where
  left := toAut_injective_of_non_trivial F G IsFundamentalGroup.non_trivial'
  right := toAut_surjective_of_isPretransitive F G IsFundamentalGroup.transitive_of_isGalois
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) [IsConnected X] : MulAction.IsPretransitive G (F.obj X) :=
  isPretransitive_of_surjective F G (toAut_bijective F G).surjective X

/-- If `G` is the fundamental group for `F`, it is isomorphic to `Aut F` as groups and
this isomorphism is also a homeomorphism (see `toAutMulEquiv_isHomeomorph`). -/
/-
**CategoryTheory.PreGaloisCategory.toAutMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.PreGaloisCategory`。
形式化陈述：toAutMulEquiv : G ≃* Aut F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.IsFundamentalGroup.toIsNaturalSMul`：∀ {
C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryTheory.Fun
ctor C FintypeCat}   {inst_1 : CategoryTheory.GaloisCateg…
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_bijective`：toAut_bijective : Func
tion.Bijective (toAut F G) where left

--- 原说明 ---
If `G` is the fundamental group for `F`, it is isomorphic to `Aut F` as groups a
nd
this isomorphism is also a homeomorphism (see `toAutMulEquiv_isHomeomorph`).
-/
noncomputable def toAutMulEquiv : G ≃* Aut F :=
  MulEquiv.ofBijective (toAut F G) (toAut_bijective F G)
/-
**CategoryTheory.PreGaloisCategory.toAut_isHomeomorph** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.PreGaloisCategory`。
形式化陈述：toAut_isHomeomorph : IsHomeomorph (toAut F G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.IsFundamentalGroup.toIsNaturalSMul`：∀ {
C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryTheory.Fun
ctor C FintypeCat}   {inst_1 : CategoryTheory.GaloisCateg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isHomeomorph_iff_continuous_bijective`：isHomeomorph_iff_continuous_bijec
tive [CompactSpace X] [T2Space Y] : IsHomeomorph f ↔ Continuous f ∧ Bijective f
· 使用定理 `CategoryTheory.PreGaloisCategory.instT2SpaceAutFunctorFintypeCat`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTheory.Functo
r C FintypeCat),   T2Space (CategoryTheory.Aut F)
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_continuous`：toAut_continuous [Top
ologicalSpace G] [IsTopologicalGroup G] [forall (X : C), ContinuousSMul G (F.obj
 X)] : Continuous (toAut F G)
· 使用定理 `CategoryTheory.PreGaloisCategory.IsFundamentalGroup.continuous_smul`：∀ {
C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryTheory.Fun
ctor C FintypeCat}   {inst_1 : CategoryTheory.GaloisCateg…
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_bijective`：toAut_bijective : Func
tion.Bijective (toAut F G) where left
-/
lemma toAut_isHomeomorph : IsHomeomorph (toAut F G) := by
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨toAut_continuous F G, toAut_bijective F G⟩
/-
**CategoryTheory.PreGaloisCategory.toAutMulEquiv_isHomeomorph** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：toAutMulEquiv_isHomeomorph : IsHomeomorph (toAutMulEquiv F G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_isHomeomorph`：toAut_isHomeomorph 
: IsHomeomorph (toAut F G)
-/
lemma toAutMulEquiv_isHomeomorph : IsHomeomorph (toAutMulEquiv F G) :=
  toAut_isHomeomorph F G

/-- If `G` is a fundamental group for `F`, it is canonically homeomorphic to `Aut F`. -/
/-
**CategoryTheory.PreGaloisCategory.toAutHomeo** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.PreGaloisCategory`。
形式化陈述：toAutHomeo : G ≃ₜ Aut F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.IsFundamentalGroup.toIsNaturalSMul`：∀ {
C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {F : CategoryTheory.Fun
ctor C FintypeCat}   {inst_1 : CategoryTheory.GaloisCateg…
· 使用引理 `CategoryTheory.PreGaloisCategory.toAut_isHomeomorph`：toAut_isHomeomorph 
: IsHomeomorph (toAut F G)

--- 原说明 ---
If `G` is a fundamental group for `F`, it is canonically homeomorphic to `Aut F`
.
-/
noncomputable def toAutHomeo : G ≃ₜ Aut F := (toAut_isHomeomorph F G).homeomorph

variable {G}

@[simp]
/-
**CategoryTheory.PreGaloisCategory.toAutMulEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.PreGaloisCategory`。
形式化陈述：toAutMulEquiv_apply (g : G) : toAutMulEquiv F G g = toAut F G g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
-/
lemma toAutMulEquiv_apply (g : G) : toAutMulEquiv F G g = toAut F G g := rfl

@[simp]
/-
**CategoryTheory.PreGaloisCategory.toAutHomeo_apply** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.PreGaloisCategory`。
形式化陈述：toAutHomeo_apply (g : G) : toAutHomeo F G g = toAut F G g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
-/
lemma toAutHomeo_apply (g : G) : toAutHomeo F G g = toAut F G g := rfl

end

end PreGaloisCategory

end CategoryTheory

