/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Action.Limits

/-!
# Examples of Galois categories and fiber functors

We show that for a group `G` the category of finite `G`-sets is a `PreGaloisCategory` and that the
forgetful functor to `FintypeCat` is a `FiberFunctor`.

The connected finite `G`-sets are precisely the ones with transitive `G`-action.

-/

@[expose] public section

universe u v w

namespace CategoryTheory

open Limits CategoryTheory.Functor PreGaloisCategory

namespace FintypeCat

/-- Complement of the image of a morphism `f : X ⟶ Y` in `FintypeCat`. -/
/-
**CategoryTheory.FintypeCat.imageComplement** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.FintypeCat`。
形式化陈述：imageComplement {X Y : FintypeCat.{u}} (f : X ⟶ Y) : FintypeCat.{u}
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Complement of the image of a morphism `f : X ⟶ Y` in `FintypeCat`.
-/
noncomputable def imageComplement {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    FintypeCat.{u} := by
  haveI : Fintype (↑(Set.range f)ᶜ) := Fintype.ofFinite _
  exact FintypeCat.of (↑(Set.range f)ᶜ)

/-- The inclusion from the complement of the image of `f : X ⟶ Y` into `Y`. -/
/-
**CategoryTheory.FintypeCat.imageComplementIncl** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.FintypeCat`。
形式化陈述：imageComplementIncl {X Y : FintypeCat.{u}} (f : X ⟶ Y) : imageComplement f
 ⟶ Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion from the complement of the image of `f : X ⟶ Y` into `Y`.
-/
noncomputable def imageComplementIncl {X Y : FintypeCat.{u}}
    (f : X ⟶ Y) : imageComplement f ⟶ Y :=
  FintypeCat.homMk Subtype.val

variable (G : Type u) [Group G]

/-- Given `f : X ⟶ Y` for `X Y : Action FintypeCat G`, the complement of the image
of `f` has a natural `G`-action. -/
/-
**CategoryTheory.FintypeCat.Action.imageComplement** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.FintypeCat.Action`。
形式化陈述：(G : Type u) → [inst : Group G] → {X Y : Action FintypeCat G} → (X ⟶ Y) → 
Action FintypeCat G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : X ⟶ Y` for `X Y : Action FintypeCat G`, the complement of the image
of `f` has a natural `G`-action.
-/
noncomputable def Action.imageComplement {X Y : Action FintypeCat G}
    (f : X ⟶ Y) : Action FintypeCat G where
  V := FintypeCat.imageComplement f.hom
  ρ := {
    toFun g := FintypeCat.homMk (fun y ↦ Subtype.mk ((Y.ρ g).hom y.val) <| by
      intro ⟨x, h⟩
      apply y.property
      use (X.ρ g⁻¹).hom x
      calc (X.ρ g⁻¹ ≫ f.hom) x
          = ((Y.ρ g⁻¹ * Y.ρ g)).hom y.val := by rw [f.comm, FintypeCat.comp_apply, h]; rfl
        _ = y.val := by
          simp [← map_mul, inv_mul_cancel, Action.ρ_one, FintypeCat.id_hom])
    map_one' := by aesop
    map_mul' := by aesop
  }

/-- The inclusion from the complement of the image of `f : X ⟶ Y` into `Y`. -/
/-
**CategoryTheory.FintypeCat.Action.imageComplementIncl** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.FintypeCat.Action`。
形式化陈述：(G : Type u) →   [inst : Group G] →     {X Y : Action FintypeCat G} → (f :
 X ⟶ Y) → CategoryTheory.FintypeCat.Action.imageComplement G f ⟶ Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion from the complement of the image of `f : X ⟶ Y` into `Y`.
-/
noncomputable def Action.imageComplementIncl {X Y : Action FintypeCat G} (f : X ⟶ Y) :
    Action.imageComplement G f ⟶ Y where
  hom := FintypeCat.imageComplementIncl f.hom
  comm _ := rfl
/-
**CategoryTheory.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.FintypeCa
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Action FintypeCat G} (f : X ⟶ Y) :
    Mono (Action.imageComplementIncl G f) := by
  apply Functor.mono_of_mono_map (forget _)
  apply ConcreteCategory.mono_of_injective
  exact Subtype.val_injective

/-- The category of finite sets has quotients by finite groups in arbitrary universes. -/
/-
**CategoryTheory.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.FintypeCa
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finite sets has quotients by finite groups in arbitrary universe
s.
-/
instance [Finite G] : HasColimitsOfShape (SingleObj G) FintypeCat.{w} := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm
/-
**CategoryTheory.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.FintypeCa
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteLimits (forget (Action FintypeCat G)) := by
  change PreservesFiniteLimits (Action.forget FintypeCat _ ⋙ FintypeCat.incl)
  apply comp_preservesFiniteLimits

/-- The category of finite `G`-sets is a `PreGaloisCategory`. -/
/-
**CategoryTheory.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.FintypeCa
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finite `G`-sets is a `PreGaloisCategory`.
-/
instance : PreGaloisCategory (Action FintypeCat G) where
  hasQuotientsByFiniteGroups _ _ _ := inferInstance
  monoInducesIsoOnDirectSummand {_ _} i _ :=
    haveI : Mono ((forget (Action FintypeCat G)).map i) := map_mono (forget _) i
    ⟨Action.imageComplement G i, Action.imageComplementIncl G i,
     ⟨isColimitOfReflects (Action.forget _ _ ⋙ FintypeCat.incl) <|
      (isColimitMapCoconeBinaryCofanEquiv (forget _) i _).symm
      (Types.isCoprodOfMono ((forget _).map i))⟩⟩

/-- The forgetful functor from finite `G`-sets to sets is a `FiberFunctor`. -/
/-
**CategoryTheory.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.FintypeCa
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from finite `G`-sets to sets is a `FiberFunctor`.
-/
noncomputable instance : FiberFunctor (Action.forget FintypeCat G) where
  preservesFiniteCoproducts := ⟨fun _ ↦ inferInstance⟩
  preservesQuotientsByFiniteGroups _ _ _ := inferInstance
  reflectsIsos := ⟨fun f (_ : IsIso f.hom) => inferInstance⟩

/-- The forgetful functor from finite `G`-sets to sets is a `FiberFunctor`. -/
/-
**CategoryTheory.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.FintypeCa
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from finite `G`-sets to sets is a `FiberFunctor`.
-/
noncomputable instance : FiberFunctor (forget₂ (Action FintypeCat G) FintypeCat) :=
  inferInstanceAs <| FiberFunctor (Action.forget FintypeCat G)

/-- The category of finite `G`-sets is a `GaloisCategory`. -/
/-
**CategoryTheory.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.FintypeCa
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finite `G`-sets is a `GaloisCategory`.
-/
instance : GaloisCategory (Action FintypeCat G) where
  hasFiberFunctor := ⟨Action.forget FintypeCat G, ⟨inferInstance⟩⟩

/-- The `G`-action on a connected finite `G`-set is transitive. -/
/-
**CategoryTheory.FintypeCat.Action.pretransitive_of_isConnected** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.FintypeCat.Action`。
形式化陈述：∀ (G : Type u) [inst : Group G] (X : Action FintypeCat G) [CategoryTheory.
PreGaloisCategory.IsConnected X],   MulAction.IsPretransitive G X.V.obj
参数：G : Type u；X : Action FintypeCat G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FintypeCat.instFiniteObj`：∀ {X : FintypeCat}, Finite X.obj
· 使用定理 `CategoryTheory.ConcreteCategory.mono_of_injective`：mono_of_injective {X 
Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono f
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `CategoryTheory.PreGaloisCategory.IsConnected.noTrivialComponent`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {X : C}   [self : CategoryT
heory.PreGaloisCategory.IsConnected X] (Y : C) (i : Y…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.PreGaloisCategory.not_initial_iff_fiber_nonempty`：not_ini
tial_iff_fiber_nonempty (X : C) : (IsInitial X -> False) ↔ Nonempty (F.obj X)
· 使用定理 `CategoryTheory.FintypeCat.instPreGaloisCategoryActionFintypeCat`：∀ (G : 
Type u) [inst : Group G], CategoryTheory.PreGaloisCategory (Action FintypeCat G)
· 使用定理 `CategoryTheory.FintypeCat.instFiberFunctorActionFintypeCatForget`：∀ (G :
 Type u) [inst : Group G], CategoryTheory.PreGaloisCategory.FiberFunctor (Action
.forget FintypeCat G)
· 使用定理 `Set.Nonempty.coe_sort`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonempty
 ↑s
· 使用定理 `MulAction.nonempty_orbit`：nonempty_orbit (a : α) : Set.Nonempty (orbit M
 a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.ConcreteCategory.isIso_iff_bijective`：isIso_iff_bijective
 [(forget C).ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bi
jective f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `FintypeCat.instFullForgetFunObjFinite`：(CategoryTheory.forget FintypeCat
).Full
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
The `G`-action on a connected finite `G`-set is transitive.
-/
theorem Action.pretransitive_of_isConnected (X : Action FintypeCat G)
    [PreGaloisCategory.IsConnected X] : MulAction.IsPretransitive G X.V where
  exists_smul_eq x y := by
    /- We show that the `G`-orbit of `x` is a non-initial subobject of `X` and hence by
    connectedness, the orbit equals `X.V`. -/
    let T : Set X.V := MulAction.orbit G x
    have : Fintype T := Fintype.ofFinite T
    let : MulAction G (FintypeCat.of T) := inferInstanceAs <| MulAction G
      ↑(MulAction.orbit G x)
    let T' : Action FintypeCat G := Action.FintypeCat.ofMulAction G (FintypeCat.of T)
    let i : T' ⟶ X := ⟨FintypeCat.homMk Subtype.val, fun _ ↦ rfl⟩
    have : Mono i := ConcreteCategory.mono_of_injective _ (Subtype.val_injective)
    have : IsIso i := by
      apply IsConnected.noTrivialComponent T' i
      apply (not_initial_iff_fiber_nonempty (Action.forget _ _) T').mpr
      exact Set.Nonempty.coe_sort (MulAction.nonempty_orbit x)
    have hb : Function.Bijective i.hom := by
      apply (ConcreteCategory.isIso_iff_bijective i.hom).mp
      exact map_isIso (forget₂ _ FintypeCat) i
    obtain ⟨⟨y', ⟨g, (hg : g • x = y')⟩⟩, (hy' : y' = y)⟩ := hb.surjective y
    use g
    exact hg.trans hy'

/-- A nonempty `G`-set with transitive `G`-action is connected. -/
/-
**CategoryTheory.FintypeCat.Action.isConnected_of_transitive** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.FintypeCat.Action`。
形式化陈述：∀ (G : Type u) [inst : Group G] (X : FintypeCat) [inst_1 : MulAction G X.o
bj] [MulAction.IsPretransitive G X.obj]   [h : Nonempty X.obj], CategoryTheory.P
reGaloisCategory.IsConnected (Action.FintypeCat.ofMulAction G X)
参数：G : Type u；X : FintypeCat；Action.FintypeCat.ofMulAction G X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.PreGaloisCategory.not_initial_of_inhabited`：not_initial_o
f_inhabited {X : C} (x : F.obj X) (h : IsInitial X) : False
· 使用定理 `CategoryTheory.FintypeCat.instPreGaloisCategoryActionFintypeCat`：∀ (G : 
Type u) [inst : Group G], CategoryTheory.PreGaloisCategory (Action FintypeCat G)
· 使用定理 `CategoryTheory.FintypeCat.instFiberFunctorActionFintypeCatForget`：∀ (G :
 Type u) [inst : Group G], CategoryTheory.PreGaloisCategory.FiberFunctor (Action
.forget FintypeCat G)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.PreGaloisCategory.not_initial_iff_fiber_nonempty`：not_ini
tial_iff_fiber_nonempty (X : C) : (IsInitial X -> False) ↔ Nonempty (F.obj X)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.ConcreteCategory.isIso_iff_bijective`：isIso_iff_bijective
 [(forget C).ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bi
jective f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `FintypeCat.instFullForgetFunObjFinite`：(CategoryTheory.forget FintypeCat
).Full
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.FintypeCat.instPreservesFiniteLimitsActionFintypeCatForge
tHomSubtypeFunObjFiniteV`：∀ (G : Type u) [inst : Group G],   CategoryTheory.Limi
ts.PreservesFiniteLimits (CategoryTheory.forget (Action FintypeCat G))
· 使用定理 `CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback`：
injective_of_mono_of_preservesPullback {X Y : C} (f : X ⟶ Y) [Mono f] [Preserves
LimitsOfShape WalkingCospan (forget C)] : Function.Injective…
· 使用定理 `CategoryTheory.Limits.FintypeCat.instPreservesFiniteLimitsFintypeCatForg
etFunObjFinite`：CategoryTheory.Limits.PreservesFiniteLimits (CategoryTheory.forg
et FintypeCat)
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Action.Hom.comm`：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, 
u_1} V] {G : Type u_2} [inst_1 : Monoid G] {M N : Action V G}   (self : M.Hom N)
 (g :…
· 使用定理 `FintypeCat.comp_apply`：comp_apply {X Y Z : FintypeCat} (f : X ⟶ Y) (g : 
Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `Action.isIso_of_hom_isIso`：∀ {V : Type u_1} [inst : CategoryTheory.Categ
ory.{v_1, u_1} V] {G : Type u_2} [inst_1 : Monoid G] {M N : Action V G}   (f : M
 ⟶ N) [Category…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.reflectsIsos`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.PreGalo
isCategory C}   {F : CategoryTheory.Functor C Fi…

--- 原说明 ---
A nonempty `G`-set with transitive `G`-action is connected.
-/
theorem Action.isConnected_of_transitive (X : FintypeCat) [MulAction G X]
    [MulAction.IsPretransitive G X] [h : Nonempty X] :
    PreGaloisCategory.IsConnected (Action.FintypeCat.ofMulAction G X) where
  notInitial := not_initial_of_inhabited (Action.forget _ _) h.some
  noTrivialComponent Y i hm hni := by
    /- We show that the induced inclusion `i.hom` of finite sets is surjective, using the
    transitivity of the `G`-action. -/
    obtain ⟨(y : Y.V)⟩ := (not_initial_iff_fiber_nonempty (Action.forget _ _) Y).mp hni
    have : IsIso i.hom := by
      refine (ConcreteCategory.isIso_iff_bijective i.hom).mpr ⟨?_, fun x' ↦ ?_⟩
      · have : Mono i.hom := map_mono (forget₂ _ _) i
        exact ConcreteCategory.injective_of_mono_of_preservesPullback i.hom
      · let x : X := i.hom y
        obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq G x x'
        use σ • y
        change (Y.ρ σ ≫ i.hom) y = x'
        rw [i.comm, FintypeCat.comp_apply]
        exact hσ
    apply isIso_of_reflects_iso i (Action.forget _ _)

/-- A nonempty finite `G`-set is connected if and only if the `G`-action is transitive. -/
/-
**CategoryTheory.FintypeCat.Action.isConnected_iff_transitive** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.FintypeCat.Action`。
形式化陈述：∀ (G : Type u) [inst : Group G] (X : Action FintypeCat G) [Nonempty X.V.ob
j],   CategoryTheory.PreGaloisCategory.IsConnected X ↔ MulAction.IsPretransitive
 G X.V.obj
参数：G : Type u；X : Action FintypeCat G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FintypeCat.Action.pretransitive_of_isConnected`：∀ (G : Ty
pe u) [inst : Group G] (X : Action FintypeCat G) [CategoryTheory.PreGaloisCatego
ry.IsConnected X],   MulAction.IsPretransitive G X.…
· 使用定理 `CategoryTheory.FintypeCat.Action.isConnected_of_transitive`：∀ (G : Type 
u) [inst : Group G] (X : FintypeCat) [inst_1 : MulAction G X.obj] [MulAction.IsP
retransitive G X.obj]   [h : Nonempty X.obj], Ca…

--- 原说明 ---
A nonempty finite `G`-set is connected if and only if the `G`-action is transiti
ve.
-/
theorem Action.isConnected_iff_transitive (X : Action FintypeCat G) [Nonempty X.V] :
    PreGaloisCategory.IsConnected X ↔ MulAction.IsPretransitive G X.V :=
  ⟨fun _ ↦ pretransitive_of_isConnected G X, fun _ ↦ isConnected_of_transitive G X.V⟩

variable {G}

/-- If `X` is a connected `G`-set and `x` is an element of `X`, `X` is isomorphic
to the quotient of `G` by the stabilizer of `x` as `G`-sets. -/
/-
**CategoryTheory.FintypeCat.isoQuotientStabilizerOfIsConnected** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.FintypeCat`。
形式化陈述：isoQuotientStabilizerOfIsConnected (X : Action FintypeCat G) [PreGaloisCat
egory.IsConnected X] (x : X.V) [Fintype (G ⧸ (MulAction.stabilizer G x))] : X ≅ 
G ⧸ₐ MulAction.stabilizer G x
参数：X : Action FintypeCat G；x : X.V；G ⧸ (MulAction.stabilizer G x)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `X` is a connected `G`-set and `x` is an element of `X`, `X` is isomorphic
to the quotient of `G` by the stabilizer of `x` as `G`-sets.
-/
noncomputable def isoQuotientStabilizerOfIsConnected (X : Action FintypeCat G)
    [PreGaloisCategory.IsConnected X] (x : X.V) [Fintype (G ⧸ (MulAction.stabilizer G x))] :
    X ≅ G ⧸ₐ MulAction.stabilizer G x :=
  haveI : MulAction.IsPretransitive G X.V := Action.pretransitive_of_isConnected G X
  let e : X.V ≃ G ⧸ MulAction.stabilizer G x :=
    (Equiv.Set.univ X.V).symm.trans <|
      (Equiv.setCongr ((MulAction.orbit_eq_univ G x).symm)).trans <|
      MulAction.orbitEquivQuotientStabilizer G x
  Iso.symm <| Action.mkIso (FintypeCat.equivEquivIso e.symm) <| fun σ : G ↦ by
    ext (a : G ⧸ MulAction.stabilizer G x)
    obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
    exact mul_smul σ τ x

end FintypeCat

end CategoryTheory

