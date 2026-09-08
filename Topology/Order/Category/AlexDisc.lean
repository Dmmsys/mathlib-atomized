/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Specialization

/-!
# Category of Alexandrov-discrete topological spaces

This defines `AlexDisc`, the category of Alexandrov-discrete topological spaces with continuous
maps, and proves it's equivalent to the category of preorders.
-/

@[expose] public section

open CategoryTheory Topology

/-- The category of Alexandrov-discrete spaces. -/
/-
**AlexDisc** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of Alexandrov-discrete spaces.
-/
structure AlexDisc extends TopCat where
  [is_alexandrovDiscrete : AlexandrovDiscrete carrier]

namespace AlexDisc

attribute [instance] is_alexandrovDiscrete

/-
**AlexDisc.** 是 Mathlib 中的一个实例，位于命名空间 `AlexDisc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort AlexDisc (Type _) :=
  ⟨fun X => X.toTopCat⟩
/-
**AlexDisc.category** 是 Mathlib 中的一个实例，位于命名空间 `AlexDisc`。
形式化陈述：category : Category AlexDisc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance category : Category AlexDisc :=
  inferInstanceAs <| Category (InducedCategory _ toTopCat)
/-
**AlexDisc.concreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `AlexDisc`。
形式化陈述：concreteCategory : ConcreteCategory AlexDisc (C(·, ·))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance concreteCategory : ConcreteCategory AlexDisc (C(·, ·)) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toTopCat) _
/-
**AlexDisc.instHasForgetToTop** 是 Mathlib 中的一个实例，位于命名空间 `AlexDisc`。
形式化陈述：instHasForgetToTop : HasForget₂ AlexDisc TopCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHasForgetToTop : HasForget₂ AlexDisc TopCat :=
  inferInstanceAs <| HasForget₂ (InducedCategory _ toTopCat) _

-- TODO: generalize to `InducedCategory.forget₂_full`?
/-
**AlexDisc.forgetToTop_full** 是 Mathlib 中的一个实例，位于命名空间 `AlexDisc`。
形式化陈述：forgetToTop_full : (forget₂ AlexDisc TopCat).Full where map_surjective f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forgetToTop_full : (forget₂ AlexDisc TopCat).Full where
  map_surjective f := ⟨InducedCategory.homMk f, rfl⟩
/-
**AlexDisc.forgetToTop_faithful** 是 Mathlib 中的一个实例，位于命名空间 `AlexDisc`。
形式化陈述：forgetToTop_faithful : (forget₂ AlexDisc TopCat).Faithful where map_inject
ive {X Y f g} h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
-/
instance forgetToTop_faithful : (forget₂ AlexDisc TopCat).Faithful where
  map_injective {X Y f g} h := by
    ext x
    exact ConcreteCategory.congr_hom h x


/-- Construct a bundled `AlexDisc` from the underlying topological space. -/
/-
**AlexDisc.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlexDisc`。
形式化陈述：of (X : Type*) [TopologicalSpace X] [AlexandrovDiscrete X] : AlexDisc wher
e toTopCat
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `AlexDisc` from the underlying topological space.
-/
abbrev of (X : Type*) [TopologicalSpace X] [AlexandrovDiscrete X] : AlexDisc where
  toTopCat := TopCat.of X
/-
**AlexDisc.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `AlexDisc`。
形式化陈述：coe_of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] : ↥(of α) =
 α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] : ↥(of α) = α := rfl
/-
**AlexDisc.forgetToTop_of** 是 Mathlib 中的一个定理，位于命名空间 `AlexDisc`。
形式化陈述：∀ (α : Type u_1) [inst : TopologicalSpace α] [inst_1 : AlexandrovDiscrete 
α],   (CategoryTheory.forget₂ AlexDisc TopCat).obj (AlexDisc.of α) = TopCat.of α
参数：α : Type u_1；CategoryTheory.forget₂ AlexDisc TopCat；AlexDisc.of α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forgetToTop_of (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] :
    (forget₂ AlexDisc TopCat).obj (of α) = TopCat.of α := rfl
/-
**AlexDisc.coe_forgetToTop** 是 Mathlib 中的一个定理，位于命名空间 `AlexDisc`。
形式化陈述：∀ (X : AlexDisc), ↑((CategoryTheory.forget₂ AlexDisc TopCat).obj X) = ↑X.t
oTopCat
参数：X : AlexDisc；(CategoryTheory.forget₂ AlexDisc TopCat).obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_forgetToTop (X : AlexDisc) : ↥((forget₂ _ TopCat).obj X) = X := rfl

/-- Constructs an equivalence between preorders from an order isomorphism between them. -/
@[simps]
/-
**AlexDisc.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `AlexDisc.Iso`。
形式化陈述：{α β : AlexDisc} → ↑α.toTopCat ≃ₜ ↑β.toTopCat → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between preorders from an order isomorphism between th
em.
-/
def Iso.mk {α β : AlexDisc} (e : α ≃ₜ β) : α ≅ β where
  hom := ConcreteCategory.ofHom (e : ContinuousMap α β)
  inv := ConcreteCategory.ofHom (e.symm : ContinuousMap β α)
  hom_inv_id := by ext; apply e.symm_apply_apply
  inv_hom_id := by ext; apply e.apply_symm_apply

end AlexDisc

/-- Sends a topological space to its specialisation order. -/
@[simps]
/-
**alexDiscEquivPreord** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：alexDiscEquivPreord : AlexDisc ≌ Preord where functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlexDisc.is_alexandrovDiscrete`：∀ (self : AlexDisc), AlexandrovDiscrete 
↑self.toTopCat

--- 原说明 ---
Sends a topological space to its specialisation order.
-/
def alexDiscEquivPreord : AlexDisc ≌ Preord where
  functor := forget₂ _ _ ⋙ topToPreord
  inverse.obj X := AlexDisc.of (WithUpperSet X)
  inverse.map f := ConcreteCategory.ofHom (WithUpperSet.map f.hom)
  unitIso := NatIso.ofComponents fun X ↦ AlexDisc.Iso.mk <| by
    dsimp; exact homeoWithUpperSetTopologyorderIso X
  counitIso := NatIso.ofComponents fun X ↦ Preord.Iso.mk <| by
    dsimp; exact (orderIsoSpecializationWithUpperSetTopology X).symm
