/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic

/-!

# Topology of fundamental group

In this file we define a natural topology on the automorphism group of a functor
`F : C ⥤ FintypeCat`: It is defined as the subspace topology induced by the natural
embedding of `Aut F` into `∀ X, Aut (F.obj X)` where
`Aut (F.obj X)` carries the discrete topology.

## References

- [Stacks 0BMQ](https://stacks.math.columbia.edu/tag/0BMQ)

-/

@[expose] public section

open Topology

universe u₁ u₂ v₁ v₂ v w

namespace CategoryTheory

namespace PreGaloisCategory

open CategoryTheory.Functor

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

/-- For a functor `F : C ⥤ FintypeCat`, the canonical embedding of `Aut F` into
the product over `Aut (F.obj X)` for all objects `X`. -/
/-
**CategoryTheory.PreGaloisCategory.autEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.PreGaloisCategory`。
形式化陈述：autEmbedding : Aut F ->* forall X, Aut (F.obj X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a functor `F : C ⥤ FintypeCat`, the canonical embedding of `Aut F` into
the product over `Aut (F.obj X)` for all objects `X`.
-/
def autEmbedding : Aut F →* ∀ X, Aut (F.obj X) :=
  MonoidHom.mk' (fun σ X ↦ σ.app X) (fun _ _ ↦ rfl)

@[simp]
/-
**CategoryTheory.PreGaloisCategory.autEmbedding_apply** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.PreGaloisCategory`。
形式化陈述：autEmbedding_apply (σ : Aut F) (X : C) : autEmbedding F σ X = σ.app X
参数：σ : Aut F；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma autEmbedding_apply (σ : Aut F) (X : C) : autEmbedding F σ X = σ.app X :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.PreGaloisCategory.autEmbedding_injective** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：autEmbedding_injective : Function.Injective (autEmbedding F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Aut.ext`：ext {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom
) : φ₁ = φ₂
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `FintypeCat.hom_ext`：hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall
 x, f x = g x) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.app_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F
 G : CategoryThe…
-/
lemma autEmbedding_injective : Function.Injective (autEmbedding F) := by
  intro σ τ h
  ext X x
  have : σ.app X = τ.app X := congr_fun h X
  rw [← Iso.app_hom, ← Iso.app_hom, this]

/-- We put the discrete topology on `F.obj X`. -/
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We put the discrete topology on `F.obj X`.
-/
scoped instance (X : C) : TopologicalSpace (F.obj X) := ⊥

@[scoped instance]
/-
**CategoryTheory.PreGaloisCategory.obj_discreteTopology** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：obj_discreteTopology (X : C) : DiscreteTopology (F.obj X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma obj_discreteTopology (X : C) : DiscreteTopology (F.obj X) := ⟨rfl⟩

/-- We put the discrete topology on `Aut (F.obj X)`. -/
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We put the discrete topology on `Aut (F.obj X)`.
-/
scoped instance (X : C) : TopologicalSpace (Aut (F.obj X)) := ⊥

/-- We give `F.obj X  ⟶ F.obj Y` the product topology. -/
@[local simp]
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We give `F.obj X  ⟶ F.obj Y` the product topology.
-/
scoped instance {X Y : C} : TopologicalSpace (F.obj X ⟶ F.obj Y) :=
  .coinduced (fun f ↦ ObjectProperty.homMk (↾f)) inferInstance
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance {X Y : C} : DiscreteTopology (F.obj X ⟶ F.obj Y) :=
  ⟨by simp [DiscreteTopology.eq_bot]⟩

@[scoped instance]
/-
**CategoryTheory.PreGaloisCategory.aut_discreteTopology** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：aut_discreteTopology (X : C) : DiscreteTopology (Aut (F.obj X))
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma aut_discreteTopology (X : C) : DiscreteTopology (Aut (F.obj X)) := ⟨rfl⟩

/-- `Aut F` is equipped with the by the embedding into `∀ X, Aut (F.obj X)` induced embedding. -/
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Aut F` is equipped with the by the embedding into `∀ X, Aut (F.obj X)` induced 
embedding.
-/
instance : TopologicalSpace (Aut F) :=
  TopologicalSpace.induced (autEmbedding F) inferInstance

/-lemma autEmbedding_range :
    Set.range (autEmbedding F) =
      ⋂ (f : Arrow C), { a | F.map f.hom ≫ (a f.right).hom = (a f.left).hom ≫ F.map f.hom } := by
  ext a
  simp only [Set.mem_range, id_obj, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun ⟨σ, h⟩ i ↦ h.symm ▸ σ.hom.naturality i.hom, fun h ↦ ?_⟩
  · use NatIso.ofComponents a (fun {X Y} f ↦ h ⟨X, Y, f⟩)
    rfl-/

set_option backward.isDefEq.respectTransparency.types false in
/-- The image of `Aut F` in `∀ X, Aut (F.obj X)` are precisely the compatible families of
automorphisms. -/
/-
**CategoryTheory.PreGaloisCategory.autEmbedding_range** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.PreGaloisCategory`。
形式化陈述：autEmbedding_range : Set.range (autEmbedding F) = ⋂ (f : Arrow C), { a | F
.map f.hom ≫ (a f.right).hom = (a f.left).hom ≫ F.map f.hom }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `FintypeCat.hom_ext`：hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall
 x, f x = g x) : f = g
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x

--- 原说明 ---
The image of `Aut F` in `∀ X, Aut (F.obj X)` are precisely the compatible famili
es of
automorphisms.
-/
lemma autEmbedding_range :
    Set.range (autEmbedding F) = ⋂ (f : Arrow C), { a | F.map f.hom ≫ (a f.right).hom =
      (a f.left).hom ≫ F.map f.hom } := by
  ext a
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun ⟨σ, h⟩ i ↦ by cat_disch, fun h ↦ ?_⟩
  exact ⟨NatIso.ofComponents a (fun {X Y} f ↦ by
    ext; simpa using ConcreteCategory.congr_hom (h ⟨X, Y, f⟩) _), rfl⟩

/-- The image of `Aut F` in `∀ X, Aut (F.obj X)` is closed. -/
/-
**CategoryTheory.PreGaloisCategory.autEmbedding_range_isClosed** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：autEmbedding_range_isClosed : IsClosed (Set.range (autEmbedding F))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.PreGaloisCategory.autEmbedding_range`：autEmbedding_range 
: Set.range (autEmbedding F) = ⋂ (f : Arrow C), { a | F.map f.hom ≫ (a f.right).
hom = (a f.left).hom ≫ F.map f.hom }
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `CategoryTheory.PreGaloisCategory.instDiscreteTopologyHomFintypeCatObj`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTheory.F
unctor C FintypeCat) {X Y : C},   DiscreteTopology (F.obj X…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用引理 `CategoryTheory.PreGaloisCategory.aut_discreteTopology`：aut_discreteTopol
ogy (X : C) : DiscreteTopology (Aut (F.obj X))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)

--- 原说明 ---
The image of `Aut F` in `∀ X, Aut (F.obj X)` is closed.
-/
lemma autEmbedding_range_isClosed : IsClosed (Set.range (autEmbedding F)) := by
  rw [autEmbedding_range]
  exact isClosed_iInter (fun f ↦ isClosed_eq (by fun_prop) (by fun_prop))
/-
**CategoryTheory.PreGaloisCategory.autEmbedding_isClosedEmbedding** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：autEmbedding_isClosedEmbedding : IsClosedEmbedding (autEmbedding F) where 
eq_induced
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.PreGaloisCategory.autEmbedding_injective`：autEmbedding_in
jective : Function.Injective (autEmbedding F)
· 使用引理 `CategoryTheory.PreGaloisCategory.autEmbedding_range_isClosed`：autEmbeddi
ng_range_isClosed : IsClosed (Set.range (autEmbedding F))
-/
lemma autEmbedding_isClosedEmbedding : IsClosedEmbedding (autEmbedding F) where
  eq_induced := rfl
  injective := autEmbedding_injective F
  isClosed_range := autEmbedding_range_isClosed F
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompactSpace (Aut F) := (autEmbedding_isClosedEmbedding F).compactSpace
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : T2Space (Aut F) :=
  T2Space.of_injective_continuous (autEmbedding_injective F) continuous_induced_dom
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TotallyDisconnectedSpace (Aut F) :=
  (autEmbedding_isClosedEmbedding F).isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMul (Aut F) :=
  (autEmbedding_isClosedEmbedding F).isInducing.continuousMul (autEmbedding F)
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousInv (Aut F) :=
  (autEmbedding_isClosedEmbedding F).isInducing.continuousInv fun _ ↦ rfl
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalGroup (Aut F) := ⟨⟩
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : SMul (Aut (F.obj X)) (F.obj X) := ⟨fun σ a => σ.hom a⟩
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : ContinuousSMul (Aut (F.obj X)) (F.obj X) := by
  constructor
  fun_prop
/-
**CategoryTheory.PreGaloisCategory.continuousSMul_aut_fiber** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：continuousSMul_aut_fiber (X : C) : ContinuousSMul (Aut F) (F.obj X) where 
continuous_smul
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `instDiscreteTopologyProd`：∀ {X : Type u} {Y : Type v} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] [DiscreteTopology X]   [DiscreteTopology
 Y], DiscreteT…
· 使用定理 `CategoryTheory.PreGaloisCategory.instDiscreteTopologyHomFintypeCatObj`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] (F : CategoryTheory.F
unctor C FintypeCat) {X Y : C},   DiscreteTopology (F.obj X…
· 使用引理 `CategoryTheory.PreGaloisCategory.obj_discreteTopology`：obj_discreteTopol
ogy (X : C) : DiscreteTopology (F.obj X)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用引理 `CategoryTheory.PreGaloisCategory.aut_discreteTopology`：aut_discreteTopol
ogy (X : C) : DiscreteTopology (Aut (F.obj X))
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
instance continuousSMul_aut_fiber (X : C) : ContinuousSMul (Aut F) (F.obj X) where
  continuous_smul := by
    let g : Aut (F.obj X) × F.obj X → F.obj X := fun ⟨σ, x⟩ ↦ σ.hom x
    let h (q : Aut F × F.obj X) : Aut (F.obj X) × F.obj X :=
      ⟨((fun p ↦ p X) ∘ autEmbedding F) q.1, q.2⟩
    change Continuous (g ∘ h)
    fun_prop

/-- If `G` is a functor of categories of finite types, the induced map `Aut F → Aut (F ⋙ G)` is
continuous. -/
/-
**CategoryTheory.PreGaloisCategory.continuous_mapAut_whiskeringRight** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：continuous_mapAut_whiskeringRight (G : FintypeCat.{w} ⥤ FintypeCat.{v}) : 
Continuous (((whiskeringRight _ _ _).obj G).mapAut F)
参数：G : FintypeCat.{w} ⥤ FintypeCat.{v}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `Topology.IsClosedEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Topo…
· 使用引理 `CategoryTheory.PreGaloisCategory.autEmbedding_isClosedEmbedding`：autEmbe
dding_isClosedEmbedding : IsClosedEmbedding (autEmbedding F) where eq_induced
· 使用定理 `continuous_pi_iff`：continuous_pi_iff : Continuous f ↔ forall i, Continuo
us fun a => f a i
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用引理 `CategoryTheory.PreGaloisCategory.aut_discreteTopology`：aut_discreteTopol
ogy (X : C) : DiscreteTopology (Aut (F.obj X))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f

--- 原说明 ---
If `G` is a functor of categories of finite types, the induced map `Aut F → Aut 
(F ⋙ G)` is
continuous.
-/
lemma continuous_mapAut_whiskeringRight (G : FintypeCat.{w} ⥤ FintypeCat.{v}) :
    Continuous (((whiskeringRight _ _ _).obj G).mapAut F) := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
    continuous_pi_iff]
  intro X
  change Continuous fun a ↦ G.mapAut (F.obj X) (autEmbedding F a X)
  fun_prop

/-- If `G` is a fully faithful functor of categories finite types, this is the automorphism of
topological groups `Aut F ≃ Aut (F ⋙ G)`. -/
/-
**CategoryTheory.PreGaloisCategory.autEquivAutWhiskerRight** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：autEquivAutWhiskerRight {G : FintypeCat.{w} ⥤ FintypeCat.{v}} (h : G.Fully
Faithful) : Aut F ≃ₜ* Aut (F ⋙ G) where __
参数：h : G.FullyFaithful。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.PreGaloisCategory.continuous_mapAut_whiskeringRight`：cont
inuous_mapAut_whiskeringRight (G : FintypeCat.{w} ⥤ FintypeCat.{v}) : Continuous
 (((whiskeringRight _ _ _).obj G).mapAut F)

--- 原说明 ---
If `G` is a fully faithful functor of categories finite types, this is the autom
orphism of
topological groups `Aut F ≃ Aut (F ⋙ G)`.
-/
noncomputable def autEquivAutWhiskerRight {G : FintypeCat.{w} ⥤ FintypeCat.{v}}
    (h : G.FullyFaithful) :
    Aut F ≃ₜ* Aut (F ⋙ G) where
  __ := (h.whiskeringRight C).autMulEquivOfFullyFaithful F
  continuous_toFun := continuous_mapAut_whiskeringRight F G
  continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := ((h.whiskeringRight C).autMulEquivOfFullyFaithful F).toEquiv)
    (continuous_mapAut_whiskeringRight F G)

variable [GaloisCategory C] [FiberFunctor F]

set_option backward.isDefEq.respectTransparency false in
/--
If `H` is an open subset of `Aut F` such that `1 ∈ H`, there exists a finite
set `I` of connected objects of `C` such that every `σ : Aut F` that induces the identity
on `F.obj X` for all `X ∈ I` is contained in `H`. In other words: The kernel
of the evaluation map `Aut F →* ∏ X : I ↦ Aut (F.obj X)` is contained in `H`.
-/
/-
**CategoryTheory.PreGaloisCategory.exists_set_ker_evaluation_subset_of_isOpen** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：exists_set_ker_evaluation_subset_of_isOpen {H : Set (Aut F)} (h1 : 1 in H)
 (h : IsOpen H) : exists (I : Set C) (_ : Fintype I), (forall X in I, IsConnecte
d X) ∧ (forall σ : Aut F, (forall X : I, σ.hom.app X = 𝟙 (F.obj X)) -> σ in H)
参数：Aut F；h1 : 1 in H；h : IsOpen H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_induced_iff`：isOpen_induced_iff [t : TopologicalSpace β] {s : Set
 α} {f : α -> β} : IsOpen[t.induced f] s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `isOpen_pi_iff`：isOpen_pi_iff {s : Set (forall a, A a)} : IsOpen s ↔ fora
ll f, f in s -> exists (I : Finset ι) (u : forall a, Set (A a)), (forall a, a in
 I …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `FintypeCat.hom_ext`：hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall
 x, f x = g x) : f = g
· 使用引理 `CategoryTheory.Limits.FintypeCat.jointly_surjective`：jointly_surjective 
{J : Type*} [SmallCategory J] [FinCategory J] (F : J ⥤ FintypeCat.{u}) (t : Coco
ne F) (h : IsColimit t) (x : t.pt) : exis…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesFiniteCoproducts`
：∀ {C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryT
heory.PreGaloisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FintypeCat.id_apply`：id_apply (X : FintypeCat) (x : X) : (𝟙 X : X -> X) 
x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `CategoryTheory.PreGaloisCategory.has_decomp_connected_components`：has_de
comp_connected_components (X : C) : exists (ι : Type) (f : ι -> C) (g : (i : ι) 
-> f i ⟶ X) (_ : IsColimit (Cofan.mk X g)), (forall i,…

--- 原说明 ---
If `H` is an open subset of `Aut F` such that `1 ∈ H`, there exists a finite
set `I` of connected objects of `C` such that every `σ : Aut F` that induces the
 identity
on `F.obj X` for all `X ∈ I` is contained in `H`. In other words: The kernel
of the evaluation map `Aut F →* ∏ X : I ↦ Aut (F.obj X)` is contained in `H`.
-/
lemma exists_set_ker_evaluation_subset_of_isOpen
    {H : Set (Aut F)} (h1 : 1 ∈ H) (h : IsOpen H) :
    ∃ (I : Set C) (_ : Fintype I), (∀ X ∈ I, IsConnected X) ∧
      (∀ σ : Aut F, (∀ X : I, σ.hom.app X = 𝟙 (F.obj X)) → σ ∈ H) := by
  obtain ⟨U, hUopen, rfl⟩ := isOpen_induced_iff.mp h
  obtain ⟨I, u, ho, ha⟩ := isOpen_pi_iff.mp hUopen 1 h1
  choose fι ff fc h4 h5 h6 using (fun X : I => has_decomp_connected_components X.val)
  refine ⟨⋃ X, Set.range (ff X), Fintype.ofFinite _, ?_, ?_⟩
  · rintro X ⟨A, ⟨Y, rfl⟩, hA2⟩
    obtain ⟨i, rfl⟩ := hA2
    exact h5 Y i
  · refine fun σ h ↦ ha (fun X XinI ↦ ?_)
    suffices h : autEmbedding F σ X = 1 by
      rw [h]
      exact (ho X XinI).right
    have h : σ.hom.app X = 𝟙 (F.obj X) := by
      have : Fintype (fι ⟨X, XinI⟩) := Fintype.ofFinite _
      ext x
      obtain ⟨⟨j⟩, a, ha : F.map _ a = x⟩ := Limits.FintypeCat.jointly_surjective
        (Discrete.functor (ff ⟨X, XinI⟩) ⋙ F) _ (Limits.isColimitOfPreserves F (h4 ⟨X, XinI⟩)) x
      rw [FintypeCat.id_apply, ← ha, NatTrans.naturality_apply]
      simp [h ⟨(ff _) j, ⟨Set.range (ff ⟨X, XinI⟩), ⟨⟨_, rfl⟩, ⟨j, rfl⟩⟩⟩⟩]
    exact Iso.ext h

open Limits

/-- The stabilizers of points in the fibers of Galois objects form a neighbourhood basis
of the identity in `Aut F`. -/
/-
**CategoryTheory.PreGaloisCategory.nhds_one_has_basis_stabilizers** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：nhds_one_has_basis_stabilizers : (nhds (1 : Aut F)).HasBasis (fun _ => Tru
e) (fun X : PointedGaloisObject F => MulAction.stabilizer (Aut F) X.pt) where me
m_iff' S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_set_ker_evaluation_subset_of_isO
pen`：exists_set_ker_evaluation_subset_of_isOpen {H : Set (Aut F)} (h1 : 1 in H) 
(h : IsOpen H) : exists (I : Set C) (_ : Fintype I), (forall X in…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `CategoryTheory.PreGaloisCategory.instHasFiniteLimits`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.PreGaloisCategory C], 
  CategoryTheory.Limits.HasFiniteLimits C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_galois_representative`：exists_ga
lois_representative (X : C) : exists (A : C) (a : F.obj A), IsGalois A ∧ Functio
n.Bijective (fun (f : A ⟶ X) => F.map f a)
· 使用定理 `trivial`：True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `FintypeCat.hom_ext`：hom_ext {X Y : FintypeCat} (f g : X ⟶ Y) (h : forall
 x, f x = g x) : f = g
· 使用引理 `CategoryTheory.PreGaloisCategory.surjective_of_nonempty_fiber_of_isConne
cted`：surjective_of_nonempty_fiber_of_isConnected {X A : C} [Nonempty (F.obj X)]
 [IsConnected A] (f : X ⟶ A) : Function.Surjective (F.map f)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用引理 `stabilizer_isOpen`：stabilizer_isOpen [DiscreteTopology X] (x : X) : IsOp
en (MulAction.stabilizer M x : Set M)
· 使用引理 `CategoryTheory.PreGaloisCategory.obj_discreteTopology`：obj_discreteTopol
ogy (X : C) : DiscreteTopology (F.obj X)
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H

--- 原说明 ---
The stabilizers of points in the fibers of Galois objects form a neighbourhood b
asis
of the identity in `Aut F`.
-/
lemma nhds_one_has_basis_stabilizers : (nhds (1 : Aut F)).HasBasis (fun _ ↦ True)
    (fun X : PointedGaloisObject F ↦ MulAction.stabilizer (Aut F) X.pt) where
  mem_iff' S := by
    rw [mem_nhds_iff]
    refine ⟨?_, ?_⟩
    · intro ⟨U, hU, hUopen, hUone⟩
      obtain ⟨I, _, hc, hmem⟩ := exists_set_ker_evaluation_subset_of_isOpen F hUone hUopen
      let P : C := ∏ᶜ fun X : I ↦ X.val
      obtain ⟨A, a, hgal, hbij⟩ := exists_galois_representative F P
      refine ⟨⟨A, a, hgal⟩, trivial, ?_⟩
      intro t (ht : t.hom.app A a = a)
      apply hU
      apply hmem
      have (X : I) : IsConnected X.val := hc X.val X.property
      have (X : I) : Nonempty (F.obj X.val) := nonempty_fiber_of_isConnected F X
      intro X
      ext x
      simp only [FintypeCat.id_apply]
      obtain ⟨z, rfl⟩ :=
        surjective_of_nonempty_fiber_of_isConnected F (Pi.π (fun X : I ↦ X.val) X) x
      obtain ⟨f, rfl⟩ := hbij.surjective z
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht]
    · intro ⟨X, _, h⟩
      exact ⟨MulAction.stabilizer (Aut F) X.pt, h, stabilizer_isOpen (Aut F) X.pt,
        Subgroup.one_mem _⟩

end PreGaloisCategory

end CategoryTheory

