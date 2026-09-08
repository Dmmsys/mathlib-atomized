/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Induced representations

Given a commutative ring `k`, a group homomorphism `φ : G →* H`, and a `k`-linear
`G`-representation `A`, this file introduces the induced representation $Ind_G^H(A)$ of `A` as
an `H`-representation.

By `ind φ A` we mean the `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ`.
We define a representation of `H` on this submodule by sending `h : H` and `⟦h₁ ⊗ₜ a⟧` to
`⟦h₁h⁻¹ ⊗ₜ a⟧`.

We also prove that the restriction functor `Rep k H ⥤ Rep k G` along `φ` is right adjoint to the
induction functor and hence that the induction functor preserves colimits.

Additionally, we show that the functor `Rep k H ⥤ ModuleCat k` sending `B : Rep k H` to
`(Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B` to `(A ⊗ Res(φ)(B))_G`. This
is used to prove Shapiro's lemma in
`Mathlib/RepresentationTheory/Homological/GroupHomology/Shapiro.lean`.

## Main definitions

* `Representation.ind φ ρ` : given a group homomorphism `φ : G →* H`, this is the induction of a
  `G`-representation `(A, ρ)` along `φ`, defined as `(k[H] ⊗[k] A)_G` and with `H`-action given by
  `h • ⟦h₁ ⊗ₜ a⟧ := ⟦h₁h⁻¹ ⊗ₜ a⟧` for `h, h₁ : H`, `a : A`.
* `Rep.indResAdjunction k φ`: given a group homomorphism `φ : G →* H`, this is the adjunction
  between the induction functor along `φ` and the restriction functor `Rep k H ⥤ Rep k G`
  along `φ`.
* `Rep.coinvariantsTensorIndNatIso φ A` : given a group homomorphism `φ : G →* H` and
  `A : Rep k G`, this is a natural isomorphism between the functor sending `B : Rep k H` to
  `(Ind(φ)(A) ⊗ B))_H` and the one sending `B` to `(A ⊗ Res(φ)(B))_G`. Used to prove Shapiro's
  lemma.

-/

@[expose] public section

open scoped MonoidAlgebra

universe t w w' u u' v v'

namespace Representation

open Finsupp

variable {k G H : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H) {A B : Type*}
  [AddCommGroup A] [Module k A] (ρ : Representation k G A)
  [AddCommGroup B] [Module k B] (τ : Representation k G B)

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this is the
`k`-module `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ`.
See `Representation.ind` for the induced `H`-representation on `IndV φ ρ`. -/
/-
**Representation.IndV** 是 Mathlib 中的一个缩写定义，位于命名空间 `Representation`。
形式化陈述：IndV
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this 
is the
`k`-module `(k[H] ⊗[k] A)_G` with the `G`-representation on `k[H]` defined by `φ
`.
See `Representation.ind` for the induced `H`-representation on `IndV φ ρ`.
-/
abbrev IndV := Coinvariants (V := TensorProduct k k[H] A)
  (Representation.tprod ((leftRegular k H).comp φ) ρ)

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this is the
`H → A →ₗ[k] (k[H] ⊗[k] A)_G` sending `h, a` to `⟦h ⊗ₜ a⟧`. -/
/-
**Representation.IndV.mk** 是 Mathlib 中的一个定义，位于命名空间 `Representation.IndV`。
形式化陈述：{k : Type u_1} →   {G : Type u_2} →     {H : Type u_3} →       [inst : Com
mRing k] →         [inst_1 : Group G] →           [inst_2 : Group H] →          
   (φ : G →* H) →               {A : Type u_4} →                 [inst_3 : AddCo
mmGroup A] →                   [inst_4 : _root_.Module k A] → (ρ : Representatio
n k G A) → H → A →ₗ[k] Representation.IndV φ ρ
参数：φ : G →* H；ρ : Representation k G A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `φ : G →* H` and a `G`-representation `(A, ρ)`, this 
is the
`H → A →ₗ[k] (k[H] ⊗[k] A)_G` sending `h, a` to `⟦h ⊗ₜ a⟧`.
-/
noncomputable abbrev IndV.mk (h : H) : A →ₗ[k] IndV φ ρ :=
  Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (.single h 1)

@[ext]
/-
**Representation.IndV.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Representation.IndV`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} {H : Type u_3} [inst : CommRing k] [inst_1
 : Group G] [inst_2 : Group H] (φ : G →* H)   {A : Type u_4} {B : Type u_5} [ins
t_3 : AddCommGroup A] [inst_4 : _root_.Module k A] (ρ : Representation k G A)   
[inst_5 : AddCommGroup B] [inst_6 : _root_.Module k B] {f g : Representation.Ind
V φ ρ →ₗ[k] B},   (∀ (h : H), f ∘ₗ Representation.IndV.mk φ ρ h = g ∘ₗ Represent
ation.IndV.mk φ ρ h) → f = g
参数：φ : G →* H；ρ : Representation k G A；∀ (h : H), f ∘ₗ Representation.IndV.mk φ 
ρ h = g ∘ₗ Representation.IndV.mk φ ρ h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Representation.Coinvariants.hom_ext`：hom_ext {f g : Coinvariants ρ ->ₗ[k
] W} (H : f ∘ₗ mk ρ = g ∘ₗ mk ρ) : f = g
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用引理 `MonoidAlgebra.lhom_ext'`：lhom_ext' {N : Type*} [Semiring R] [AddCommMono
id N] [Module R N] [Module R S] ⦃f g : S[M] ->ₗ[R] N⦄ (H : forall (x : M), Linea
rMap.comp f (…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
-/
lemma IndV.hom_ext {f g : IndV φ ρ →ₗ[k] B}
    (hfg : ∀ h : H, f ∘ₗ IndV.mk φ ρ h = g ∘ₗ IndV.mk φ ρ h) : f = g :=
  Coinvariants.hom_ext <| TensorProduct.ext <| MonoidAlgebra.lhom_ext' fun h =>
    LinearMap.ext_ring <| hfg h

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`. -/
@[simps]
/-
**Representation.ind** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：ind : Representation k H (IndV φ ρ) where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H
` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`.
-/
noncomputable def ind : Representation k H (IndV φ ρ) where
  toFun h :=
    Coinvariants.map _ _ ⟨(MonoidAlgebra.mapDomainLinearMap k k fun x => x * h⁻¹).rTensor _,
    fun _ => by ext; simp [mul_assoc]⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [IndV, mul_assoc]
/-
**Representation.ind_mk** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：ind_mk (h₁ h₂ : H) (a : A) : ind φ ρ h₁ (IndV.mk _ _ h₂ a) = IndV.mk _ _ (
h₂ * h₁⁻¹) a
参数：h₁ h₂ : H；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.ind_apply`：∀ {k : Type u_1} {G : Type u_2} {H : Type u_3}
 [inst : CommRing k] [inst_1 : Group G] [inst_2 : Group H] (φ : G →* H)   {A : T
ype u_4} [inst…
· 使用引理 `MonoidAlgebra.mapDomainLinearMap_single`：mapDomainLinearMap_single (f : 
M -> N) (s : S) (m : M) : mapDomainLinearMap R S f (single m s) = single (f m) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ind_mk (h₁ h₂ : H) (a : A) :
    ind φ ρ h₁ (IndV.mk _ _ h₂ a) = IndV.mk _ _ (h₂ * h₁⁻¹) a := by
  simp

end Representation

namespace Rep

open CategoryTheory Finsupp

variable {k : Type u} {G : Type v} {H : Type v'} [CommRing k] [Group G] [Group H] (φ : G →* H)
  (A : Rep.{w} k G)

section Ind

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`. -/
/-
**Rep.ind** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：ind : Rep k H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H
` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`.
-/
noncomputable abbrev ind : Rep k H := Rep.of (A.ρ.ind φ)

/-- Given a group homomorphism `φ : G →* H`, a morphism of `G`-representations `f : A ⟶ B` induces
a morphism of `H`-representations `(k[H] ⊗[k] A)_G ⟶ (k[H] ⊗[k] B)_G`. -/
/-
**Rep.indMap** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：indMap {A B : Rep k G} (f : A ⟶ B) : ind φ A ⟶ ind φ B
参数：f : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `φ : G →* H`, a morphism of `G`-representations `f : 
A ⟶ B` induces
a morphism of `H`-representations `(k[H] ⊗[k] A)_G ⟶ (k[H] ⊗[k] B)_G`.
-/
noncomputable def indMap {A B : Rep k G} (f : A ⟶ B) : ind φ A ⟶ ind φ B := Rep.ofHom
  ⟨Representation.Coinvariants.map _ _ ⟨f.hom.toLinearMap.lTensor _, by
    simp [LinearMap.lTensor_comp_map, f.hom.2, LinearMap.map_comp_lTensor]⟩,
    fun g ↦ by ext; simp⟩

variable (k) in
/-- Given a group homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the induced `H`-representation `ind φ A`, with action on maps induced by left tensoring. -/
@[implicit_reducible, simps obj map]
/-
**Rep.indFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：indFunctor : Rep.{w} k G ⥤ Rep k H where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `φ : G →* H`, this is the functor sending a `G`-repre
sentation `A`
to the induced `H`-representation `ind φ A`, with action on maps induced by left
 tensoring.
-/
noncomputable def indFunctor : Rep.{w} k G ⥤ Rep k H where
  obj A := ind φ A
  map f := indMap φ f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

end Ind
section Adjunction

open Representation

variable (B : Rep k H)

/-- Given a group homomorphism `φ : G →* H`, an `H`-representation `B`, and a `G`-representation
`A`, there is a `k`-linear equivalence between the `H`-representation morphisms `ind φ A ⟶ B` and
the `G`-representation morphisms `A ⟶ B`. -/
@[simps]
/-
**Rep.indResHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：indResHomEquiv (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H) : (in
d φ A ⟶ B) ≃ₗ[k] (A ⟶ res φ B) where toFun f
参数：A : Rep.{max w v' u} k G；B : Rep.{max w v' u} k H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `φ : G →* H`, an `H`-representation `B`, and a `G`-re
presentation
`A`, there is a `k`-linear equivalence between the `H`-representation morphisms 
`ind φ A ⟶ B` and
the `G`-representation morphisms `A ⟶ B`.
-/
noncomputable def indResHomEquiv (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H) :
    (ind φ A ⟶ B) ≃ₗ[k] (A ⟶ res φ B) where
  toFun f := Rep.ofHom ⟨f.hom.toLinearMap ∘ₗ IndV.mk φ A.ρ 1, fun g ↦ by
    ext x
    have := (hom_comm_apply f (φ g) (IndV.mk φ A.ρ 1 x)).symm
    simp_all [← Coinvariants.mk_inv_tmul] ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨Representation.Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => B.ρ h⁻¹ ∘ₗ f.hom.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
    fun g ↦ by
      ext h x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [ofMulAction_single, mul_inv_rev, hom_comm_apply f g], fun g ↦ by ext; simp⟩
  left_inv f := by
    ext h a
    simpa using (hom_comm_apply f h⁻¹ (IndV.mk φ A.ρ 1 a)).symm
  right_inv _ := by ext; simp

variable (k) in
/-- Given a group homomorphism `φ : G →* H`, the induction functor `Rep k G ⥤ Rep k H` is left
adjoint to the restriction functor along `φ`. -/
/-
**Rep.indResAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：indResAdjunction : indFunctor k φ ⊣ resFunctor.{max w v' u} φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group homomorphism `φ : G →* H`, the induction functor `Rep k G ⥤ Rep k 
H` is left
adjoint to the restriction functor along `φ`.
-/
noncomputable def indResAdjunction : indFunctor k φ ⊣ resFunctor.{max w v' u} φ :=
  Adjunction.mkOfHomEquiv {
    homEquiv A B := (indResHomEquiv φ A B).toEquiv
    homEquiv_naturality_left_symm _ _ := by
      change (indResHomEquiv φ _ _).symm (_ ≫ _) = _
      ext; simp [indMap, indResHomEquiv]
    homEquiv_naturality_right := by intros; rfl }

open Finsupp
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (indFunctor.{max u v' w} k φ).IsLeftAdjoint :=
  (indResAdjunction k φ).isLeftAdjoint
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (resFunctor.{max u v' w} (k := k) φ).IsRightAdjoint :=
  (indResAdjunction k φ).isRightAdjoint

end Adjunction

section

variable {G H : Type u} [Group G] [Group H] (φ : G →* H) (A : Rep k G) (B : Rep k H)

open Representation

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear map
`(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to `⟦a ⊗ ρ(h)(b)⟧` for all
`h : H`, `a : A`, and `b : B`. -/
/-
**Rep.coinvariantsTensorIndHom** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coinvariantsTensorIndHom : ((coinvariantsTensor k H).obj (ind φ A)).obj B 
⟶ ((coinvariantsTensor k G).obj A).obj (res φ B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`
-linear map
`(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to `⟦a ⊗ ρ(h)(b
)⟧` for all
`h : H`, `a : A`, and `b : B`.
-/
noncomputable def coinvariantsTensorIndHom :
    ((coinvariantsTensor k H).obj (ind φ A)).obj B ⟶
      ((coinvariantsTensor k G).obj A).obj (res φ B) :=
  ModuleCat.ofHom <| Coinvariants.lift _ (TensorProduct.lift <| Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ <| fun g ↦
      (coinvariantsTensorMk A (res φ B)).compl₂ (B.ρ g)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
      fun g ↦ by ext; simpa [coinvariantsTensorMk, Coinvariants.mk_eq_iff]
        using! Coinvariants.sub_mem_ker _ _) fun _ ↦ by
    simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V, tensor_ρ, res_obj_ρ,
      Functor.postcompose₂_obj_obj_obj_obj, coinvariantsFunctor_obj_carrier,
      tprod_apply, ind_apply]
    ext; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {A B} in
/-
**Rep.coinvariantsTensorIndHom_mk_tmul_indVMk** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：coinvariantsTensorIndHom_mk_tmul_indVMk (h : H) (x : A) (y : B) : coinvari
antsTensorIndHom φ A B (coinvariantsTensorMk _ _ (IndV.mk φ _ h x) y) = coinvari
antsTensorMk _ _ x (B.ρ h y)
参数：h : H；x : A；y : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma coinvariantsTensorIndHom_mk_tmul_indVMk (h : H) (x : A) (y : B) :
    coinvariantsTensorIndHom φ A B (coinvariantsTensorMk _ _ (IndV.mk φ _ h x) y) =
      coinvariantsTensorMk _ _ x (B.ρ h y) := by
  simp [coinvariantsTensorIndHom, coinvariantsTensorMk]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear map
`(A ⊗ Res(φ)(B))_G ⟶ (Ind(φ)(A) ⊗ B))_H` sending `⟦a ⊗ₜ b⟧` to `⟦1 ⊗ₜ a⟧ ⊗ₜ b` for all
`a : A`, and `b : B`. -/
/-
**Rep.coinvariantsTensorIndInv** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coinvariantsTensorIndInv : ((coinvariantsTensor k G).obj A).obj (res φ B) 
⟶ ((coinvariantsTensor k H).obj (ind φ A)).obj B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`
-linear map
`(A ⊗ Res(φ)(B))_G ⟶ (Ind(φ)(A) ⊗ B))_H` sending `⟦a ⊗ₜ b⟧` to `⟦1 ⊗ₜ a⟧ ⊗ₜ b` f
or all
`a : A`, and `b : B`.
-/
noncomputable def coinvariantsTensorIndInv :
    ((coinvariantsTensor k G).obj A).obj (res φ B) ⟶
      ((coinvariantsTensor k H).obj (ind φ A)).obj B :=
  ModuleCat.ofHom <| Coinvariants.lift _ (TensorProduct.lift <|
    (coinvariantsTensorMk (ind (k := k) φ A) B) ∘ₗ IndV.mk _ _ 1) fun s ↦ by
    simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V, tensor_ρ, tprod_apply,
      MonoidHom.coe_comp, Function.comp_apply]
    ext x y
    simpa [Coinvariants.mk_eq_iff, coinvariantsTensorMk] using
      Coinvariants.mem_ker_of_eq (φ s) (IndV.mk φ A.ρ (1 : H) x ⊗ₜ[k] y) _ <| by
      simp [← Coinvariants.mk_inv_tmul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {A B} in
/-
**Rep.coinvariantsTensorIndInv_mk_tmul_indMk** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：coinvariantsTensorIndInv_mk_tmul_indMk (x : A) (y : B) : coinvariantsTenso
rIndInv φ A B (Coinvariants.mk (A.ρ.tprod (Rep.ρ (res φ B))) x otimesₜ y) = coin
variantsTensorMk _ _ (IndV.mk φ _ 1 x) y
参数：x : A；y : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coinvariantsTensorIndInv_mk_tmul_indMk (x : A) (y : B) :
    coinvariantsTensorIndInv φ A B (Coinvariants.mk
      (A.ρ.tprod (Rep.ρ (res φ B))) <| x ⊗ₜ y) =
      coinvariantsTensorMk _ _ (IndV.mk φ _ 1 x) y := by
  simp [coinvariantsTensorIndInv, coinvariantsTensorMk]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear
isomorphism `(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to `⟦a ⊗ ρ(h)(b)⟧`
for all `h : H`, `a : A`, and `b : B`. -/
@[simps]
/-
**Rep.coinvariantsTensorIndIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coinvariantsTensorIndIso : ((coinvariantsTensor k H).obj (ind φ A)).obj B 
≅ ((coinvariantsTensor k G).obj A).obj (res φ B) where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`
-linear
isomorphism `(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to 
`⟦a ⊗ ρ(h)(b)⟧`
for all `h : H`, `a : A`, and `b : B`.
-/
noncomputable def coinvariantsTensorIndIso :
    ((coinvariantsTensor k H).obj (ind φ A)).obj B ≅
      ((coinvariantsTensor k G).obj A).obj (res φ B) where
  hom := coinvariantsTensorIndHom φ A B
  inv := coinvariantsTensorIndInv φ A B
  hom_inv_id := by
    ext h a b
    simpa [coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom, Coinvariants.mk_eq_iff] using
        Coinvariants.mem_ker_of_eq h (IndV.mk φ _ h a ⊗ₜ[k] b) _ <| by simp
  inv_hom_id := by
    ext
    simp [coinvariantsTensorIndInv, coinvariantsTensorMk, coinvariantsTensorIndHom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H` and `A : Rep k G`, the functor `Rep k H ⥤ ModuleCat k` sending
`B ↦ (Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B ↦ (A ⊗ Res(φ)(B))_G`. -/
@[simps! hom_app inv_app]
/-
**Rep.coinvariantsTensorIndNatIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：coinvariantsTensorIndNatIso : (coinvariantsTensor k H).obj (ind φ A) ≅ res
Functor φ ⋙ (coinvariantsTensor k G).obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a group hom `φ : G →* H` and `A : Rep k G`, the functor `Rep k H ⥤ ModuleC
at k` sending
`B ↦ (Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B ↦ (A ⊗ Re
s(φ)(B))_G`.
-/
noncomputable def coinvariantsTensorIndNatIso :
    (coinvariantsTensor k H).obj (ind φ A) ≅ resFunctor φ ⋙ (coinvariantsTensor k G).obj A :=
  NatIso.ofComponents (fun B => coinvariantsTensorIndIso φ A B) fun {X Y} f => by
    ext
    simp [coinvariantsTensorIndHom, coinvariantsTensorMk, hom_comm_apply]

end
end Rep

