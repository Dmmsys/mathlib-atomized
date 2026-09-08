/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro, Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.ApplyFun

/-!
# Products and coproducts in the category of topological spaces
-/

@[expose] public section

open CategoryTheory Limits Set TopologicalSpace Topology

universe v u w

noncomputable section

namespace TopCat

variable {J : Type v} [Category.{w} J]

/-- The projection from the product as a bundled continuous map. -/
/-
**TopCat.pi** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from the product as a bundled continuous map.
-/
abbrev piπ {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : TopCat.of (∀ i, α i) ⟶ α i :=
  ofHom ⟨fun f => f i, continuous_apply i⟩

/-- The explicit fan of a family of topological spaces given by the pi type. -/
@[simps! pt π_app]
/-
**TopCat.piFan** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：piFan {ι : Type v} (α : ι -> TopCat.{max v u}) : Fan α
参数：α : ι -> TopCat.{max v u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit fan of a family of topological spaces given by the pi type.
-/
def piFan {ι : Type v} (α : ι → TopCat.{max v u}) : Fan α :=
  Fan.mk (TopCat.of (∀ i, α i)) (piπ.{v, u} α)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed fan is indeed a limit -/
/-
**TopCat.piFanIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：piFanIsLimit {ι : Type v} (α : ι -> TopCat.{max v u}) : IsLimit (piFan α) 
where lift S
参数：α : ι -> TopCat.{max v u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed fan is indeed a limit
-/
def piFanIsLimit {ι : Type v} (α : ι → TopCat.{max v u}) : IsLimit (piFan α) where
  lift S := ofHom
    { toFun := fun s i => S.π.app ⟨i⟩ s
      continuous_toFun := continuous_pi (fun i => (S.π.app ⟨i⟩).hom.2) }
  uniq := by
    intro S m h
    ext x
    funext i
    simp [ContinuousMap.coe_mk, ← h ⟨i⟩]
  fac _ _ := rfl

/-- The product is homeomorphic to the product of the underlying spaces,
equipped with the product topology.
-/
/-
**TopCat.piIsoPi** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：piIsoPi {ι : Type v} (α : ι -> TopCat.{max v u}) : ∏ᶜ α ≅ TopCat.of (foral
l i, α i)
参数：α : ι -> TopCat.{max v u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product is homeomorphic to the product of the underlying spaces,
equipped with the product topology.
-/
def piIsoPi {ι : Type v} (α : ι → TopCat.{max v u}) : ∏ᶜ α ≅ TopCat.of (∀ i, α i) :=
  (limit.isLimit _).conePointUniqueUpToIso (piFanIsLimit.{v, u} α)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**TopCat.piIsoPi_inv_** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piIsoPi_inv_π {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) :
    (piIsoPi α).inv ≫ Pi.π α i = piπ α i := by simp [piIsoPi]
/-
**TopCat.piIsoPi_inv_** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piIsoPi_inv_π_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : ∀ i, α i) :
    (Pi.π α i :) ((piIsoPi α).inv x) = x i :=
  ConcreteCategory.congr_hom (piIsoPi_inv_π α i) x
/-
**TopCat.piIsoPi_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：piIsoPi_hom_apply {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) (x : (∏
ᶜ α : TopCat.{max v u})) : (piIsoPi α).hom x i = (Pi.π α i :) x
参数：α : ι -> TopCat.{max v u}；i : ι；x : (∏ᶜ α : TopCat.{max v u})。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem piIsoPi_hom_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι)
    (x : (∏ᶜ α : TopCat.{max v u})) : (piIsoPi α).hom x i = (Pi.π α i :) x := rfl

/-- The inclusion to the coproduct as a bundled continuous map. -/
/-
**TopCat.sigma** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion to the coproduct as a bundled continuous map.
-/
abbrev sigmaι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) : α i ⟶ TopCat.of (Σ i, α i) := by
  refine ofHom (ContinuousMap.mk ?_ ?_)
  · apply Sigma.mk i
  · continuity

/-- The explicit cofan of a family of topological spaces given by the sigma type. -/
@[simps! pt ι_app]
/-
**TopCat.sigmaCofan** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：sigmaCofan {ι : Type v} (α : ι -> TopCat.{max v u}) : Cofan α
参数：α : ι -> TopCat.{max v u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit cofan of a family of topological spaces given by the sigma type.
-/
def sigmaCofan {ι : Type v} (α : ι → TopCat.{max v u}) : Cofan α :=
  Cofan.mk (TopCat.of (Σ i, α i)) (sigmaι α)

/-- The constructed cofan is indeed a colimit -/
/-
**TopCat.sigmaCofanIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：sigmaCofanIsColimit {ι : Type v} (β : ι -> TopCat.{max v u}) : IsColimit (
sigmaCofan β) where desc S
参数：β : ι -> TopCat.{max v u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed cofan is indeed a colimit
-/
def sigmaCofanIsColimit {ι : Type v} (β : ι → TopCat.{max v u}) : IsColimit (sigmaCofan β) where
  desc S := ofHom
    { toFun := fun (s : of (Σ i, β i)) => S.ι.app ⟨s.1⟩ s.2
      continuous_toFun := by continuity }
  uniq := by
    intro S m h
    ext ⟨i, x⟩
    simp only [← h]
    congr
  fac s j := by
    cases j
    cat_disch

/-- The coproduct is homeomorphic to the disjoint union of the topological spaces.
-/
/-
**TopCat.sigmaIsoSigma** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：sigmaIsoSigma {ι : Type v} (α : ι -> TopCat.{max v u}) : ∐ α ≅ TopCat.of (
Σ i, α i)
参数：α : ι -> TopCat.{max v u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coproduct is homeomorphic to the disjoint union of the topological spaces.
-/
def sigmaIsoSigma {ι : Type v} (α : ι → TopCat.{max v u}) : ∐ α ≅ TopCat.of (Σ i, α i) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (sigmaCofanIsColimit.{v, u} α)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**TopCat.sigmaIsoSigma_hom_** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaIsoSigma_hom_ι {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) :
    Sigma.ι α i ≫ (sigmaIsoSigma α).hom = sigmaι α i := by simp [sigmaIsoSigma]
/-
**TopCat.sigmaIsoSigma_hom_** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaIsoSigma_hom_ι_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).hom ((Sigma.ι α i :) x) = Sigma.mk i x :=
  ConcreteCategory.congr_hom (sigmaIsoSigma_hom_ι α i) x
/-
**TopCat.sigmaIsoSigma_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：sigmaIsoSigma_inv_apply {ι : Type v} (α : ι -> TopCat.{max v u}) (i : ι) (
x : α i) : (sigmaIsoSigma α).inv ⟨i, x⟩ = (Sigma.ι α i :) x
参数：α : ι -> TopCat.{max v u}；i : ι；x : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.sigmaIsoSigma_hom_ι_apply`：sigmaIsoSigma_hom_ι_apply {ι : Type v}
 (α : ι -> TopCat.{max v u}) (i : ι) (x : α i) : (sigmaIsoSigma α).hom ((Sigma.ι
 α i :) x) = Sigma.mk …
· 使用定理 `TopCat.comp_app`：comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (
x : X) : (f ≫ g : X -> Z) x = g (f x)
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem sigmaIsoSigma_inv_apply {ι : Type v} (α : ι → TopCat.{max v u}) (i : ι) (x : α i) :
    (sigmaIsoSigma α).inv ⟨i, x⟩ = (Sigma.ι α i :) x := by
  rw [← sigmaIsoSigma_hom_ι_apply, ← comp_app, ← comp_app, Iso.hom_inv_id,
    Category.comp_id]

section Prod

/-- The first projection from the product. -/
/-
**TopCat.prodFst** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
形式化陈述：prodFst {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection from the product.
-/
abbrev prodFst {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ X :=
  ofHom { toFun := Prod.fst }

/-- The second projection from the product. -/
/-
**TopCat.prodSnd** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat`。
形式化陈述：prodSnd {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection from the product.
-/
abbrev prodSnd {X Y : TopCat.{u}} : TopCat.of (X × Y) ⟶ Y :=
  ofHom { toFun := Prod.snd }

/-- The explicit binary cofan of `X, Y` given by `X × Y`. -/
/-
**TopCat.prodBinaryFan** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：prodBinaryFan (X Y : TopCat.{u}) : BinaryFan X Y
参数：X Y : TopCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit binary cofan of `X, Y` given by `X × Y`.
-/
def prodBinaryFan (X Y : TopCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk prodFst prodSnd

/-- The constructed binary fan is indeed a limit -/
/-
**TopCat.prodBinaryFanIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：prodBinaryFanIsLimit (X Y : TopCat.{u}) : IsLimit (prodBinaryFan X Y) wher
e lift
参数：X Y : TopCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed binary fan is indeed a limit
-/
def prodBinaryFanIsLimit (X Y : TopCat.{u}) : IsLimit (prodBinaryFan X Y) where
  lift := fun S : BinaryFan X Y => ofHom { toFun s := (S.fst s, S.snd s) }
  fac := by
    rintro S (_ | _) <;> {dsimp; ext; rfl}
  uniq := by
    intro S m h
    ext x
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): used to be part of `ext x`
    refine Prod.ext ?_ ?_
    · specialize h ⟨WalkingPair.left⟩
      apply_fun fun e => e x at h
      exact h
    · specialize h ⟨WalkingPair.right⟩
      apply_fun fun e => e x at h
      exact h

/-- The homeomorphism between `X ⨯ Y` and the set-theoretic product of `X` and `Y`,
equipped with the product topology.
-/
/-
**TopCat.prodIsoProd** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：prodIsoProd (X Y : TopCat.{u}) : X ⨯ Y ≅ TopCat.of (X × Y)
参数：X Y : TopCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism between `X ⨯ Y` and the set-theoretic product of `X` and `Y`,
equipped with the product topology.
-/
def prodIsoProd (X Y : TopCat.{u}) : X ⨯ Y ≅ TopCat.of (X × Y) :=
  (limit.isLimit _).conePointUniqueUpToIso (prodBinaryFanIsLimit X Y)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**TopCat.prodIsoProd_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：prodIsoProd_hom_fst (X Y : TopCat.{u}) : (prodIsoProd X Y).hom ≫ prodFst =
 Limits.prod.fst
参数：X Y : TopCat.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_inv_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
-/
theorem prodIsoProd_hom_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).hom ≫ prodFst = Limits.prod.fst := by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**TopCat.prodIsoProd_hom_snd** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：prodIsoProd_hom_snd (X Y : TopCat.{u}) : (prodIsoProd X Y).hom ≫ prodSnd =
 Limits.prod.snd
参数：X Y : TopCat.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_inv_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
-/
theorem prodIsoProd_hom_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).hom ≫ prodSnd = Limits.prod.snd := by
  simp [← Iso.eq_inv_comp, prodIsoProd]
  rfl

-- Note that `(x : X ⨯ Y)` would mean `(x : ↑X × ↑Y)` below:
/-
**TopCat.prodIsoProd_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：prodIsoProd_hom_apply {X Y : TopCat.{u}} (x : ↑(X ⨯ Y)) : (prodIsoProd X Y
).hom x = ((Limits.prod.fst : X ⨯ Y ⟶ _) x, (Limits.prod.snd : X ⨯ Y ⟶ _) x)
参数：x : ↑(X ⨯ Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem prodIsoProd_hom_apply {X Y : TopCat.{u}} (x : ↑(X ⨯ Y)) :
    (prodIsoProd X Y).hom x = ((Limits.prod.fst : X ⨯ Y ⟶ _) x,
    (Limits.prod.snd : X ⨯ Y ⟶ _) x) := rfl

@[reassoc (attr := simp), elementwise]
/-
**TopCat.prodIsoProd_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：prodIsoProd_inv_fst (X Y : TopCat.{u}) : (prodIsoProd X Y).inv ≫ Limits.pr
od.fst = prodFst
参数：X Y : TopCat.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.prodIsoProd_hom_fst`：prodIsoProd_hom_fst (X Y : TopCat.{u}) : (pr
odIsoProd X Y).hom ≫ prodFst = Limits.prod.fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodIsoProd_inv_fst (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.fst = prodFst := by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp), elementwise]
/-
**TopCat.prodIsoProd_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：prodIsoProd_inv_snd (X Y : TopCat.{u}) : (prodIsoProd X Y).inv ≫ Limits.pr
od.snd = prodSnd
参数：X Y : TopCat.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.prodIsoProd_hom_snd`：prodIsoProd_hom_snd (X Y : TopCat.{u}) : (pr
odIsoProd X Y).hom ≫ prodSnd = Limits.prod.snd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodIsoProd_inv_snd (X Y : TopCat.{u}) :
    (prodIsoProd X Y).inv ≫ Limits.prod.snd = prodSnd := by simp [Iso.inv_comp_eq]
/-
**TopCat.prod_topology** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：prod_topology {X Y : TopCat.{u}} : (X ⨯ Y).str = induced (Limits.prod.fst 
: X ⨯ Y ⟶ _) X.str ⊓ induced (Limits.prod.snd : X ⨯ Y ⟶ _) Y.str
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
-/
theorem prod_topology {X Y : TopCat.{u}} :
    (X ⨯ Y).str =
      induced (Limits.prod.fst : X ⨯ Y ⟶ _) X.str ⊓
        induced (Limits.prod.snd : X ⨯ Y ⟶ _) Y.str := by
  let homeo := homeoOfIso (prodIsoProd X Y)
  refine homeo.isInducing.eq_induced.trans ?_
  change induced homeo (_ ⊓ _) = _
  simp [induced_compose]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.range_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：range_prod_map {W X Y Z : TopCat.{u}} (f : W ⟶ Y) (g : X ⟶ Z) : Set.range 
(Limits.prod.map f g) = (Limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' Set.range f inter (Lim
its.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' Set.range g
参数：f : W ⟶ Y；g : X ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.Concrete.limit_ext`：limit_ext [HasLimit F] (x y : 
ToType (limit F)) : (forall j, limit.π F j x = limit.π F j y) -> x = y
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `TopCat.instIsRightAdjointForgetContinuousMapCarrier`：(CategoryTheory.for
get TopCat).IsRightAdjoint
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.prodIsoProd_inv_fst_apply`：∀ (X Y : TopCat) (x : ↑X × ↑Y),   (Cat
egoryTheory.ConcreteCategory.hom CategoryTheory.Limits.prod.fst)       ((Categor
yTheory.ConcreteCatego…
· 使用定理 `TopCat.prodIsoProd_inv_snd_apply`：∀ (X Y : TopCat) (x : ↑X × ↑Y),   (Cat
egoryTheory.ConcreteCategory.hom CategoryTheory.Limits.prod.snd)       ((Categor
yTheory.ConcreteCatego…
-/
theorem range_prod_map {W X Y Z : TopCat.{u}} (f : W ⟶ Y) (g : X ⟶ Z) :
    Set.range (Limits.prod.map f g) =
      (Limits.prod.fst : Y ⨯ Z ⟶ _) ⁻¹' Set.range f ∩
        (Limits.prod.snd : Y ⨯ Z ⟶ _) ⁻¹' Set.range g := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp_rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_range, ← ConcreteCategory.comp_apply,
      Limits.prod.map_fst, Limits.prod.map_snd, ConcreteCategory.comp_apply, exists_apply_eq_apply,
      and_self_iff]
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    use (prodIsoProd W X).inv (x₁, x₂)
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · rw [← ConcreteCategory.comp_apply]
      erw [Limits.prod.map_fst]
      rw [ConcreteCategory.comp_apply, TopCat.prodIsoProd_inv_fst_apply]
      exact hx₁
    · rw [← ConcreteCategory.comp_apply]
      erw [Limits.prod.map_snd]
      rw [ConcreteCategory.comp_apply, TopCat.prodIsoProd_inv_snd_apply]
      exact hx₂
/-
**TopCat.isInducing_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isInducing_prodMap {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : Is
Inducing f) (hg : IsInducing g) : IsInducing (Limits.prod.map f g)
参数：hf : IsInducing f；hg : IsInducing g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.prod_topology`：prod_topology {X Y : TopCat.{u}} : (X ⨯ Y).str = i
nduced (Limits.prod.fst : X ⨯ Y ⟶ _) X.str ⊓ induced (Limits.prod.snd : X ⨯ Y ⟶ 
_) Y.str
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
-/
theorem isInducing_prodMap {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsInducing f)
    (hg : IsInducing g) : IsInducing (Limits.prod.map f g) := by
  constructor
  simp_rw [prod_topology, induced_inf, induced_compose, ← coe_comp,
    prod.map_fst, prod.map_snd, coe_comp, ← induced_compose (g := f), ← induced_compose (g := g)]
  rw [← hf.eq_induced, ← hg.eq_induced]
/-
**TopCat.isEmbedding_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：isEmbedding_prodMap {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : I
sEmbedding f) (hg : IsEmbedding g) : IsEmbedding (Limits.prod.map f g)
参数：hf : IsEmbedding f；hg : IsEmbedding g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TopCat.isInducing_prodMap`：isInducing_prodMap {W X Y Z : TopCat.{u}} {f 
: W ⟶ X} {g : Y ⟶ Z} (hf : IsInducing f) (hg : IsInducing g) : IsInducing (Limit
s.prod.map f g)
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopCat.mono_iff_injective`：mono_iff_injective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.prod.map_mono`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)   [CategoryThe
ory.Mono f] [CategoryTheo…
-/
theorem isEmbedding_prodMap {W X Y Z : TopCat.{u}} {f : W ⟶ X} {g : Y ⟶ Z} (hf : IsEmbedding f)
    (hg : IsEmbedding g) : IsEmbedding (Limits.prod.map f g) :=
  ⟨isInducing_prodMap hf.isInducing hg.isInducing, by
    have := (TopCat.mono_iff_injective _).mpr hf.injective
    have := (TopCat.mono_iff_injective _).mpr hg.injective
    exact (TopCat.mono_iff_injective _).mp inferInstance⟩

end Prod

/-- The binary coproduct cofan in `TopCat`. -/
/-
**TopCat.binaryCofan** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：(X Y : TopCat) → CategoryTheory.Limits.BinaryCofan X Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary coproduct cofan in `TopCat`.
-/
protected def binaryCofan (X Y : TopCat.{u}) : BinaryCofan X Y :=
  BinaryCofan.mk (ofHom ⟨Sum.inl, by fun_prop⟩) (ofHom ⟨Sum.inr, by fun_prop⟩)

set_option backward.isDefEq.respectTransparency.types false in
/-- The constructed binary coproduct cofan in `TopCat` is the coproduct. -/
/-
**TopCat.binaryCofanIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：binaryCofanIsColimit (X Y : TopCat.{u}) : IsColimit (TopCat.binaryCofan X 
Y)
参数：X Y : TopCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed binary coproduct cofan in `TopCat` is the coproduct.
-/
def binaryCofanIsColimit (X Y : TopCat.{u}) : IsColimit (TopCat.binaryCofan X Y) := by
  refine Limits.BinaryCofan.isColimitMk (fun s => ofHom
    { toFun := Sum.elim s.inl s.inr, continuous_toFun := ?_ }) ?_ ?_ ?_
  · fun_prop
  · intro s
    ext
    rfl
  · intro s
    ext
    rfl
  · intro s m h₁ h₂
    ext (x | x)
    exacts [ConcreteCategory.congr_hom h₁ x, ConcreteCategory.congr_hom h₂ x]

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.binaryCofan_isColimit_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopCat`。
形式化陈述：binaryCofan_isColimit_iff {X Y : TopCat.{u}} (c : BinaryCofan X Y) : Nonem
pty (IsColimit c) ↔ IsOpenEmbedding c.inl ∧ IsOpenEmbedding c.inr ∧ IsCompl (ran
ge c.inl) (range c.inr)
参数：c : BinaryCofan X Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
· 使用定理 `Topology.IsOpenEmbedding.inl`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inl
· 使用定理 `Topology.IsOpenEmbedding.inr`：∀ {X : Type u} {Y : Type v} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y], Topology.IsOpenEmbedding Sum.inr
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `eq_compl_iff_isCompl`：eq_compl_iff_isCompl : x = yᶜ ↔ IsCompl x y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_compl_eq`：image_compl_eq {f : α -> β} {s : Set α} (H : Bijecti
ve f) : f '' sᶜ = (f '' s)ᶜ
· 使用定理 `Homeomorph.bijective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Bijective ⇑h
· 使用定理 `Set.compl_range_inr`：compl_range_inr : (range (Sum.inr : β -> α oplus β)
)ᶜ = range (Sum.inl : α -> α oplus β)
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `or_not`：or_not {p : Prop} : p ∨ ¬p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsOpen.continuousOn_iff`：IsOpen.continuousOn_iff (hs : IsOpen s) : Conti
nuousOn f s ↔ forall ⦃a⦄, a in s -> ContinuousAt f a
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
（共 58 条，此处仅展示前 30 条）
-/
theorem binaryCofan_isColimit_iff {X Y : TopCat.{u}} (c : BinaryCofan X Y) :
    Nonempty (IsColimit c) ↔
      IsOpenEmbedding c.inl ∧ IsOpenEmbedding c.inr ∧ IsCompl (range c.inl) (range c.inr) := by
  classical
    constructor
    · rintro ⟨h⟩
      rw [← show _ = c.inl from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.left⟩,
        ← show _ = c.inr from
          h.comp_coconePointUniqueUpToIso_inv (binaryCofanIsColimit X Y) ⟨WalkingPair.right⟩]
      dsimp
      refine ⟨(homeoOfIso <| h.coconePointUniqueUpToIso
        (binaryCofanIsColimit X Y)).symm.isOpenEmbedding.comp .inl,
          (homeoOfIso <| h.coconePointUniqueUpToIso
            (binaryCofanIsColimit X Y)).symm.isOpenEmbedding.comp .inr, ?_⟩
      rw [Set.range_comp, ← eq_compl_iff_isCompl]
      conv_rhs => rw [Set.range_comp]
      erw [← Set.image_compl_eq (homeoOfIso <| h.coconePointUniqueUpToIso
            (binaryCofanIsColimit X Y)).symm.bijective, Set.compl_range_inr, Set.image_comp]
    · rintro ⟨h₁, h₂, h₃⟩
      have : ∀ x, x ∈ Set.range c.inl ∨ x ∈ Set.range c.inr := by
        rw [eq_compl_iff_isCompl.mpr h₃.symm]
        exact fun _ => or_not
      refine ⟨BinaryCofan.IsColimit.mk _ ?_ ?_ ?_ ?_⟩
      · intro T f g
        refine ofHom (ContinuousMap.mk ?_ ?_)
        · exact fun x =>
            if h : x ∈ Set.range c.inl then f ((Equiv.ofInjective _ h₁.injective).symm ⟨x, h⟩)
            else g ((Equiv.ofInjective _ h₂.injective).symm ⟨x, (this x).resolve_left h⟩)
        rw [continuous_iff_continuousAt]
        intro x
        by_cases h : x ∈ Set.range c.inl
        · revert h x
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_domRestrict]
            convert_to Continuous (f ∘ h₁.isEmbedding.toHomeomorph.symm)
            · ext ⟨x, hx⟩
              exact dif_pos hx
            fun_prop
          · exact h₁.isOpen_range
        · revert h x
          simp only [← mem_compl_iff]
          apply (IsOpen.continuousOn_iff _).mp
          · rw [continuousOn_iff_continuous_domRestrict]
            have : ∀ a, a ∉ Set.range c.inl → a ∈ Set.range c.inr := by
              rintro a (h : a ∈ (Set.range c.inl)ᶜ)
              rwa [eq_compl_iff_isCompl.mpr h₃.symm]
            convert_to! Continuous
                (g ∘ h₂.isEmbedding.toHomeomorph.symm ∘ Subtype.map _ this)
            · ext ⟨x, hx⟩
              exact dif_neg hx
            apply Continuous.comp
            · exact g.hom.continuous_toFun
            · apply Continuous.comp (by fun_prop)
              rw [IsEmbedding.subtypeVal.isInducing.continuous_iff]
              exact continuous_subtype_val
          · change IsOpen (Set.range c.inl)ᶜ
            rw [← eq_compl_iff_isCompl.mpr h₃.symm]
            exact h₂.isOpen_range
      · intro T f g
        ext x
        simp
      · intro T f g
        ext x
        dsimp
        rw [dif_neg]
        · exact congr_arg g (Equiv.ofInjective_symm_apply _ _)
        · rintro ⟨y, e⟩
          have : c.inr x ∈ Set.range c.inl ⊓ Set.range c.inr := ⟨⟨_, e⟩, ⟨_, rfl⟩⟩
          rwa [disjoint_iff.mp h₃.1] at this
      · rintro T _ _ m rfl rfl
        ext x
        change m x = dite _ _ _
        split_ifs <;> exact congr_arg _ (Equiv.apply_ofInjective_symm _ ⟨_, _⟩).symm

end TopCat

