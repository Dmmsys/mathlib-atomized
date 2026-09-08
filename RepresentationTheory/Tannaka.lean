/-
Copyright (c) 2025 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.RepresentationTheory.FDRep

/-!
# Tannaka duality for finite groups

In this file we prove Tannaka duality for finite groups.

The theorem can be formulated as follows: for any integral domain `k`, a finite group `G` can be
recovered from `FDRep k G`, the monoidal category of finite-dimensional `k`-linear representations
of `G`, and the monoidal forgetful functor `forget : FDRep k G ⥤ FGModuleCat k`.

The main result is the isomorphism `equiv : G ≃* Aut (forget k G)`.

## Reference

<https://math.leidenuniv.nl/scripties/1bachCommelin.pdf>
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory ModuleCat Finset Pi

universe u

namespace TannakaDuality

namespace FiniteGroup

variable {k G : Type u} [CommRing k] [Group G]

section definitions

/-
**TannakaDuality.FiniteGroup.** 是 Mathlib 中的一个实例，位于命名空间 `TannakaDuality.FiniteGr
oup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (FDRep k G) (FGModuleCat k)).Monoidal :=
  inferInstanceAs <| (Action.forget _ _).Monoidal

variable (k G) in
/-- The monoidal forgetful functor from `FDRep k G` to `FGModuleCat k`. -/
/-
**TannakaDuality.FiniteGroup.forget** 是 Mathlib 中的一个定义，位于命名空间 `TannakaDuality.Fi
niteGroup`。
形式化陈述：forget
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal

--- 原说明 ---
The monoidal forgetful functor from `FDRep k G` to `FGModuleCat k`.
-/
def forget := LaxMonoidalFunctor.of (forget₂ (FDRep k G) (FGModuleCat k))
/-
**TannakaDuality.FiniteGroup.forget_obj** 是 Mathlib 中的一个定理，位于命名空间 `TannakaDualit
y.FiniteGroup`。
形式化陈述：∀ {k G : Type u} [inst : CommRing k] [inst_1 : Group G] (X : FDRep k G),  
 (TannakaDuality.FiniteGroup.forget k G).obj X = X.V
参数：X : FDRep k G；TannakaDuality.FiniteGroup.forget k G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
-/
@[simp] lemma forget_obj (X : FDRep k G) : (forget k G).obj X = X.V := rfl
/-
**TannakaDuality.FiniteGroup.forget_map** 是 Mathlib 中的一个定理，位于命名空间 `TannakaDualit
y.FiniteGroup`。
形式化陈述：∀ {k G : Type u} [inst : CommRing k] [inst_1 : Group G] (X Y : FDRep k G) 
(f : X ⟶ Y),   (TannakaDuality.FiniteGroup.forget k G).map f = f.hom
参数：X Y : FDRep k G；f : X ⟶ Y；TannakaDuality.FiniteGroup.forget k G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
-/
@[simp] lemma forget_map (X Y : FDRep k G) (f : X ⟶ Y) : (forget k G).map f = f.hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Definition of `equivHom g : Aut (forget k G)` by its components. -/
@[simps]
/-
**TannakaDuality.FiniteGroup.equivApp** 是 Mathlib 中的一个定义，位于命名空间 `TannakaDuality.
FiniteGroup`。
形式化陈述：equivApp (g : G) (X : FDRep k G) : X.V ≅ X.V where hom
参数：g : G；X : FDRep k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of `equivHom g : Aut (forget k G)` by its components.
-/
def equivApp (g : G) (X : FDRep k G) : X.V ≅ X.V where
  hom := InducedCategory.homMk (ofHom (X.ρ g))
  inv := InducedCategory.homMk (ofHom (X.ρ g⁻¹))
  hom_inv_id := by
    ext x
    simp
  inv_hom_id := by
    ext x
    simp

set_option backward.isDefEq.respectTransparency.types false in
variable (k G) in
/-- The group homomorphism `G →* Aut (forget k G)` shown to be an isomorphism. -/
@[simps]
/-
**TannakaDuality.FiniteGroup.equivHom** 是 Mathlib 中的一个定义，位于命名空间 `TannakaDuality.
FiniteGroup`。
形式化陈述：equivHom : G ->* Aut (forget k G) where toFun g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal

--- 原说明 ---
The group homomorphism `G →* Aut (forget k G)` shown to be an isomorphism.
-/
def equivHom : G →* Aut (forget k G) where
  toFun g :=
    LaxMonoidalFunctor.isoOfComponents (equivApp g) (fun f ↦ (f.comm g).symm) rfl (by intros; rfl)
  map_one' := by ext; simp; rfl
  map_mul' _ _ := by ext; simp; rfl

/-- The representation on `G → k` induced by multiplication on the right in `G`. -/
/-
**TannakaDuality.FiniteGroup.rightRegular** 是 Mathlib 中的一个定义，位于命名空间 `TannakaDual
ity.FiniteGroup`。
形式化陈述：rightRegular : Representation k G (G -> k) where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representation on `G → k` induced by multiplication on the right in `G`.
-/
def rightRegular : Representation k G (G → k) where
  toFun s :=
  { toFun f t := f (t * s)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

@[simp]
/-
**TannakaDuality.FiniteGroup.rightRegular_apply** 是 Mathlib 中的一个引理，位于命名空间 `Tanna
kaDuality.FiniteGroup`。
形式化陈述：rightRegular_apply (s t : G) (f : G -> k) : rightRegular s f t = f (t * s)
参数：s t : G；f : G -> k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightRegular_apply (s t : G) (f : G → k) : rightRegular s f t = f (t * s) := rfl

/-- The representation on `G → k` induced by multiplication on the left in `G`. -/
/-
**TannakaDuality.FiniteGroup.leftRegular** 是 Mathlib 中的一个定义，位于命名空间 `TannakaDuali
ty.FiniteGroup`。
形式化陈述：leftRegular : Representation k G (G -> k) where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representation on `G → k` induced by multiplication on the left in `G`.
-/
def leftRegular : Representation k G (G → k) where
  toFun s :=
  { toFun f t := f (s⁻¹ * t)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

@[simp]
/-
**TannakaDuality.FiniteGroup.leftRegular_apply** 是 Mathlib 中的一个引理，位于命名空间 `Tannak
aDuality.FiniteGroup`。
形式化陈述：leftRegular_apply (s t : G) (f : G -> k) : leftRegular s f t = f (s⁻¹ * t)
参数：s t : G；f : G -> k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftRegular_apply (s t : G) (f : G → k) : leftRegular s f t = f (s⁻¹ * t) := rfl

/-- The right regular representation `rightRegular` on `G → k` as a `FDRep k G`. -/
@[simp]
/-
**TannakaDuality.FiniteGroup.rightFDRep** 是 Mathlib 中的一个定义，位于命名空间 `TannakaDualit
y.FiniteGroup`。
形式化陈述：rightFDRep [Finite G] : FDRep k G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right regular representation `rightRegular` on `G → k` as a `FDRep k G`.
-/
def rightFDRep [Finite G] : FDRep k G := FDRep.of rightRegular

end definitions

variable [Finite G]

set_option backward.isDefEq.respectTransparency false in
/-
**TannakaDuality.FiniteGroup.equivHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `Tanna
kaDuality.FiniteGroup`。
形式化陈述：equivHom_injective [Nontrivial k] : Function.Injective (equivHom k G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `TannakaDuality.FiniteGroup.equivHom_apply`：∀ (k G : Type u) [inst : Comm
Ring k] [inst_1 : Group G] (g : G),   (TannakaDuality.FiniteGroup.equivHom k G) 
g =     CategoryTheory.LaxMonoi…
· 使用定理 `CategoryTheory.LaxMonoidalFunctor.isoOfComponents_hom_hom_app`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Mono
idalCategory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `TannakaDuality.FiniteGroup.equivApp_hom`：∀ {k G : Type u} [inst : CommRi
ng k] [inst_1 : Group G] (g : G) (X : FDRep k G),   (TannakaDuality.FiniteGroup.
equivApp g X).hom = CategoryT…
· 使用定理 `CategoryTheory.InducedCategory.homMk_hom`：∀ {C : Type u₁} {D : Type u₂} 
[inst : CategoryTheory.Category.{v, u₂} D] {F : C → D}   {X Y : CategoryTheory.I
nducedCategory D F} (f : F X ⟶…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Pi.single_congr`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] {i₁ i₂ : ι},   i₁ = i₂ → ∀ {x₁ x₂ : M}, x₁ = x₂ → ∀ {j₁ j₂ : ι
}, j₁…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivHom_injective [Nontrivial k] : Function.Injective (equivHom k G) := by
  intro s t h
  classical
  apply_fun (fun x ↦ (x.hom.hom.app rightFDRep).hom (single t 1) 1) at h
  simp_all [single_apply]

/-- The `FDRep k G` morphism induced by multiplication on `G → k`. -/
/-
**TannakaDuality.FiniteGroup.mulRepHom** 是 Mathlib 中的一个定义，位于命名空间 `TannakaDuality
.FiniteGroup`。
形式化陈述：mulRepHom : rightFDRep (k
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal

--- 原说明 ---
The `FDRep k G` morphism induced by multiplication on `G → k`.
-/
def mulRepHom : rightFDRep (k := k) (G := G) ⊗ rightFDRep ⟶ rightFDRep where
  hom := InducedCategory.homMk (ofHom (LinearMap.mul' k (G → k)))
  comm := by
    intro
    ext u
    refine TensorProduct.induction_on u rfl (fun _ _ ↦ rfl) (fun _ _ hx hy ↦ ?_)
    simp only [map_add, hx, hy]

/-- The `rightFDRep` component of `η : Aut (forget k G)` preserves multiplication -/
/-
**TannakaDuality.FiniteGroup.map_mul_toRightFDRepComp** 是 Mathlib 中的一个引理，位于命名空间 
`TannakaDuality.FiniteGroup`。
形式化陈述：map_mul_toRightFDRepComp (η : Aut (forget k G)) (f g : G -> k) : let α : (
G -> k) ->ₗ[k] (G -> k)
参数：η : Aut (forget k G)；f g : G -> k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.IsMonoidal.tensor`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.LaxMonoidalFunctor.Hom.isMonoidal`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory 
C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The `rightFDRep` component of `η : Aut (forget k G)` preserves multiplication
-/
lemma map_mul_toRightFDRepComp (η : Aut (forget k G)) (f g : G → k) :
    let α : (G → k) →ₗ[k] (G → k) := (η.hom.hom.app rightFDRep).hom.hom
    α (f * g) = (α f) * (α g) := by
  have nat := η.hom.hom.naturality mulRepHom
  have tensor (X Y) : η.hom.hom.app (X ⊗ Y) = (η.hom.hom.app X ⊗ₘ η.hom.hom.app Y) :=
    η.hom.isMonoidal.tensor X Y
  rw [tensor] at nat
  exact ConcreteCategory.congr_hom ((CategoryTheory.forget _).congr_map nat) (f ⊗ₜ[k] g)

set_option backward.isDefEq.respectTransparency false in
/-- The `rightFDRep` component of `η : Aut (forget k G)` gives rise to
an algebra morphism `(G → k) →ₐ[k] (G → k)`. -/
/-
**TannakaDuality.FiniteGroup.algHomOfRightFDRepComp** 是 Mathlib 中的一个定义，位于命名空间 `T
annakaDuality.FiniteGroup`。
形式化陈述：algHomOfRightFDRepComp (η : Aut (forget k G)) : (G -> k) ->ₐ[k] (G -> k)
参数：η : Aut (forget k G)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
· 使用引理 `TannakaDuality.FiniteGroup.map_mul_toRightFDRepComp`：map_mul_toRightFDRe
pComp (η : Aut (forget k G)) (f g : G -> k) : let α : (G -> k) ->ₗ[k] (G -> k)

--- 原说明 ---
The `rightFDRep` component of `η : Aut (forget k G)` gives rise to
an algebra morphism `(G → k) →ₐ[k] (G → k)`.
-/
def algHomOfRightFDRepComp (η : Aut (forget k G)) : (G → k) →ₐ[k] (G → k) := by
  let α : (G → k) →ₗ[k] (G → k) := (η.hom.hom.app rightFDRep).hom.hom
  let α_inv : (G → k) →ₗ[k] (G → k) := (η.inv.hom.app rightFDRep).hom.hom
  refine AlgHom.ofLinearMap α ?_ (map_mul_toRightFDRepComp η)
  suffices α (α_inv 1) = (1 : G → k) by
    have h := this
    rwa [← one_mul (α_inv 1), map_mul_toRightFDRepComp, h, mul_one] at this
  have := η.inv_hom_id
  apply_fun (fun x ↦ (x.hom.app rightFDRep).hom (1 : G → k)) at this
  exact this

/-- For `v : X` and `G` a finite group, the `G`-equivariant linear map from the right
regular representation `rightFDRep` to `X` sending `single 1 1` to `v`. -/
@[simps]
/-
**TannakaDuality.FiniteGroup.sumSMulInv** 是 Mathlib 中的一个定义，位于命名空间 `TannakaDualit
y.FiniteGroup`。
形式化陈述：sumSMulInv [Fintype G] {X : FDRep k G} (v : X) : (G -> k) ->ₗ[k] X where t
oFun f
参数：v : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `v : X` and `G` a finite group, the `G`-equivariant linear map from the righ
t
regular representation `rightFDRep` to `X` sending `single 1 1` to `v`.
-/
def sumSMulInv [Fintype G] {X : FDRep k G} (v : X) : (G → k) →ₗ[k] X where
  toFun f := ∑ s : G, (f s) • (X.ρ s⁻¹ v)
  map_add' _ _ := by simp [add_smul, sum_add_distrib]
  map_smul' _ _ := by simp [smul_sum, smul_smul]

omit [Finite G] in
/-
**TannakaDuality.FiniteGroup.sumSMulInv_single_id** 是 Mathlib 中的一个引理，位于命名空间 `Tan
nakaDuality.FiniteGroup`。
形式化陈述：sumSMulInv_single_id [Fintype G] [DecidableEq G] {X : FDRep k G} (v : X) :
 ∑ s : G, (single 1 1 : G -> k) s • (X.ρ s⁻¹) v = v
参数：v : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fintype.sum_single_smul`：sum_single_smul {R : Type*} [Semiring R] [Modul
e R α] (f : ι -> α) (r : R) (i₀ : ι) : ∑ i, (Pi.single (M
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sumSMulInv_single_id [Fintype G] [DecidableEq G] {X : FDRep k G} (v : X) :
    ∑ s : G, (single 1 1 : G → k) s • (X.ρ s⁻¹) v = v := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- For `v : X` and `G` a finite group, the representation morphism from the right
regular representation `rightFDRep` to `X` sending `single 1 1` to `v`. -/
@[simps]
/-
**TannakaDuality.FiniteGroup.ofRightFDRep** 是 Mathlib 中的一个定义，位于命名空间 `TannakaDual
ity.FiniteGroup`。
形式化陈述：ofRightFDRep [Fintype G] (X : FDRep k G) (v : X) : rightFDRep ⟶ X where ho
m
参数：X : FDRep k G；v : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `v : X` and `G` a finite group, the representation morphism from the right
regular representation `rightFDRep` to `X` sending `single 1 1` to `v`.
-/
def ofRightFDRep [Fintype G] (X : FDRep k G) (v : X) : rightFDRep ⟶ X where
  hom := InducedCategory.homMk (ofHom (sumSMulInv v))
  comm t := by
    ext f
    let φ_term (X : FDRep k G) (f : G → k) v s := (f s) • (X.ρ s⁻¹ v)
    have := sum_map univ (mulRightEmbedding t⁻¹) (φ_term X (rightRegular t f) v)
    simpa [φ_term] using! this

set_option backward.isDefEq.respectTransparency false in
/-
**TannakaDuality.FiniteGroup.toRightFDRepComp_injective** 是 Mathlib 中的一个引理，位于命名空
间 `TannakaDuality.FiniteGroup`。
形式化陈述：toRightFDRepComp_injective {η₁ η₂ : Aut (forget k G)} (h : η₁.hom.hom.app 
rightFDRep = η₂.hom.hom.app rightFDRep) : η₁ = η₂
参数：forget k G；h : η₁.hom.hom.app rightFDRep = η₂.hom.hom.app rightFDRep。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
· 使用引理 `CategoryTheory.Aut.ext`：ext {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom
) : φ₁ = φ₂
· 使用引理 `CategoryTheory.LaxMonoidalFunctor.hom_ext`：hom_ext {F G : LaxMonoidalFun
ctor C D} {α β : F ⟶ G} (h : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FGModuleCat.hom_ext`：∀ {R : Type u} [inst : Ring R] {V W : FGModuleCat R
} {f g : V ⟶ W},   ModuleCat.Hom.hom f.hom = ModuleCat.Hom.hom g.hom → f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TannakaDuality.FiniteGroup.ofRightFDRep_hom`：∀ {k G : Type u} [inst : Co
mmRing k] [inst_1 : Group G] [inst_2 : Finite G] [inst_3 : Fintype G] (X : FDRep
 k G)   (v : ↑X.V),   (TannakaDua…
· 使用定理 `CategoryTheory.InducedCategory.homMk_hom`：∀ {C : Type u₁} {D : Type u₂} 
[inst : CategoryTheory.Category.{v, u₂} D] {F : C → D}   {X Y : CategoryTheory.I
nducedCategory D F} (f : F X ⟶…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `TannakaDuality.FiniteGroup.sumSMulInv_apply`：∀ {k G : Type u} [inst : Co
mmRing k] [inst_1 : Group G] [inst_2 : Fintype G] {X : FDRep k G} (v : ↑X.V) (f 
: G → k),   (TannakaDuality.Finit…
· 使用引理 `Fintype.sum_single_smul`：sum_single_smul {R : Type*} [Semiring R] [Modul
e R α] (f : ι -> α) (r : R) (i₀ : ι) : ∑ i, (Pi.single (M
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma toRightFDRepComp_injective {η₁ η₂ : Aut (forget k G)}
    (h : η₁.hom.hom.app rightFDRep = η₂.hom.hom.app rightFDRep) : η₁ = η₂ := by
  have := Fintype.ofFinite G
  classical
  ext X v
  have h1 := η₁.hom.hom.naturality (ofRightFDRep X v)
  have h2 := η₂.hom.hom.naturality (ofRightFDRep X v)
  rw [h, ← h2] at h1
  simpa using congr(($h1).hom (single 1 1))

/-- `leftRegular` as a morphism `rightFDRep k G ⟶ rightFDRep k G` in `FDRep k G`. -/
/-
**TannakaDuality.FiniteGroup.leftRegularFDRepHom** 是 Mathlib 中的一个定义，位于命名空间 `Tann
akaDuality.FiniteGroup`。
形式化陈述：leftRegularFDRepHom (s : G) : End (rightFDRep : FDRep k G) where hom
参数：s : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`leftRegular` as a morphism `rightFDRep k G ⟶ rightFDRep k G` in `FDRep k G`.
-/
def leftRegularFDRepHom (s : G) : End (rightFDRep : FDRep k G) where
  hom := InducedCategory.homMk (ofHom (leftRegular s))
  comm _ := by
    ext f
    funext _
    apply congrArg f
    exact mul_assoc ..

set_option backward.isDefEq.respectTransparency false in
/-
**TannakaDuality.FiniteGroup.toRightFDRepComp_in_rightRegular** 是 Mathlib 中的一个引理
，位于命名空间 `TannakaDuality.FiniteGroup`。
形式化陈述：toRightFDRepComp_in_rightRegular [IsDomain k] (η : Aut (forget k G)) : exi
sts (s : G), (η.hom.hom.app rightFDRep).hom.hom = rightRegular s
参数：η : Aut (forget k G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
· 使用引理 `AlgHom.eq_piEvalAlgHom`：AlgHom.eq_piEvalAlgHom {k G : Type*} [CommSemiri
ng k] [NoZeroDivisors k] [Nontrivial k] [Finite G] (φ : (G -> k) ->ₐ[k] k) : exi
sts (s : G),…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.basisFun_apply`：basisFun_apply [DecidableEq η] (i) : basisFun R η i =
 Pi.single i 1
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.evalAlgHom_apply`：∀ {ι : Type u_1} (R : Type u_2) (A : ι → Type u_3) 
[inst : CommSemiring R] [inst_1 : (i : ι) → Semiring (A i)]   [inst_2 : (i : ι) 
→ Algebra…
· 使用定理 `Pi.single_congr`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] {i₁ i₂ : ι},   i₁ = i₂ → ∀ {x₁ x₂ : M}, x₁ = x₂ → ∀ {j₁ j₂ : ι
}, j₁…
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma toRightFDRepComp_in_rightRegular [IsDomain k] (η : Aut (forget k G)) :
    ∃ (s : G), (η.hom.hom.app rightFDRep).hom.hom = rightRegular s := by
  classical
  obtain ⟨s, hs⟩ := ((evalAlgHom _ _ 1).comp (algHomOfRightFDRepComp η)).eq_piEvalAlgHom
  refine ⟨s, (basisFun k G).ext fun u ↦ ?_⟩
  simp only [rightFDRep, forget_obj]
  ext t
  have nat := η.hom.hom.naturality (leftRegularFDRepHom t⁻¹)
  calc
    _ = leftRegular t⁻¹ ((η.hom.hom.app rightFDRep).hom (single u 1)) 1 := by simp
    _ = (η.hom.hom.app rightFDRep).hom (leftRegular t⁻¹ (single u 1)) 1 :=
      congrFun congr(($nat.symm).hom (single u 1)) 1
    _ = evalAlgHom _ _ s (leftRegular t⁻¹ (single u 1)) :=
      congr($hs (leftRegular t⁻¹ (single u 1)))
    _ = _ := by by_cases u = t * s <;> simp_all

set_option backward.isDefEq.respectTransparency.types false in
/-
**TannakaDuality.FiniteGroup.equivHom_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Tann
akaDuality.FiniteGroup`。
形式化陈述：equivHom_surjective [IsDomain k] : Function.Surjective (equivHom k G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
· 使用引理 `TannakaDuality.FiniteGroup.toRightFDRepComp_in_rightRegular`：toRightFDRe
pComp_in_rightRegular [IsDomain k] (η : Aut (forget k G)) : exists (s : G), (η.h
om.hom.app rightFDRep).hom.hom = rightRegular s
· 使用引理 `TannakaDuality.FiniteGroup.toRightFDRepComp_injective`：toRightFDRepComp_
injective {η₁ η₂ : Aut (forget k G)} (h : η₁.hom.hom.app rightFDRep = η₂.hom.hom
.app rightFDRep) : η₁ = η₂
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma equivHom_surjective [IsDomain k] : Function.Surjective (equivHom k G) := by
  intro η
  obtain ⟨s, h⟩ := toRightFDRepComp_in_rightRegular η
  exact ⟨s, toRightFDRepComp_injective (InducedCategory.hom_ext (hom_ext h.symm))⟩

variable (k G) in
/-- Tannaka duality for finite groups:

A finite group `G` is isomorphic to `Aut (forget k G)`, where `k` is any integral domain,
and `forget k G` is the monoidal forgetful functor `FDRep k G ⥤ FGModuleCat k G`. -/
/-
**TannakaDuality.FiniteGroup.equiv** 是 Mathlib 中的一个定义，位于命名空间 `TannakaDuality.Fin
iteGroup`。
形式化陈述：equiv [IsDomain k] : G ≃* Aut (forget k G)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal

--- 原说明 ---
Tannaka duality for finite groups:

A finite group `G` is isomorphic to `Aut (forget k G)`, where `k` is any integra
l domain,
and `forget k G` is the monoidal forgetful functor `FDRep k G ⥤ FGModuleCat k G`
.
-/
def equiv [IsDomain k] : G ≃* Aut (forget k G) :=
  MulEquiv.ofBijective (equivHom k G) ⟨equivHom_injective, equivHom_surjective⟩

end FiniteGroup

end TannakaDuality

end

