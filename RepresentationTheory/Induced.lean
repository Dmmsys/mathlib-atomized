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

variable {k G H : Type*} [CommRing k] [Group G] [Group H] (φ : G ->* H) {A B : Type*}
  [AddCommGroup A] [Module k A] (ρ : Representation k G A)
  [AddCommGroup B] [Module k B] (τ : Representation k G B)

/--
Definition of `IndV` / `IndV` 的定义

English:
abbreviation IndV
  body: Coinvariants (V := TensorProduct k k[H] A)
  (Representation.tprod ((leftRegular k H).comp φ) ρ)

中文:
缩写 IndV
  定义体: Coinvariants (V := TensorProduct k k[H] A)
  (Representation.tprod ((leftRegular k H).comp φ) ρ)

Depends on / 依赖: Coinvariants, TensorProduct
-/
abbrev IndV := Coinvariants (V := TensorProduct k k[H] A)
  (Representation.tprod ((leftRegular k H).comp φ) ρ)

/--
Definition of `IndV.mk` / `IndV.mk` 的定义

English:
abbreviation IndV.mk
  signature: (h : H)
  body: Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (.single h 1)

@[ext]

中文:
缩写 IndV.mk
  签名: (h : H)
  定义体: Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (.single h 1)

@[ext]

Depends on / 依赖: Coinvariants, Coinvariants.mk, TensorProduct, TensorProduct.mk, single
-/
noncomputable abbrev IndV.mk (h : H) : A ->ₗ[k] IndV φ ρ :=
  Coinvariants.mk _ ∘ₗ TensorProduct.mk k _ _ (.single h 1)

@[ext]
/--
lemma `IndV.hom_ext` / 引理 `IndV.hom_ext`

English:
lemma IndV.hom_ext
  statement: {f g : IndV φ ρ ->ₗ[k] B}
  proof: Coinvariants.hom_ext TensorProduct.ext MonoidAlgebra.lhom_ext' fun h =>
LinearMap.ext_ring hfg h

中文:
引理 IndV.hom_ext
  结论: {f g : IndV φ ρ ->ₗ[k] B}
  证明: Coinvariants.hom_ext TensorProduct.ext MonoidAlgebra.lhom_ext' fun h =>
LinearMap.ext_ring hfg h

Depends on / 依赖: Coinvariants, Coinvariants.hom_ext, LinearMap, LinearMap.ext_ring, MonoidAlgebra, MonoidAlgebra.lhom_ext, TensorProduct, TensorProduct.ext, ext_ring, hom_ext, lhom_ext
-/
lemma IndV.hom_ext {f g : IndV φ ρ ->ₗ[k] B}
    (hfg : forall h : H, f ∘ₗ IndV.mk φ ρ h = g ∘ₗ IndV.mk φ ρ h) : f = g :=
Coinvariants.hom_ext TensorProduct.ext MonoidAlgebra.lhom_ext' fun h =>
LinearMap.ext_ring hfg h

/-- Given a group homomorphism `φ : G →* H` and a `G`-representation `A`, this is
`(k[H] ⊗[k] A)_G` equipped with the `H`-representation defined by sending `h : H` and `⟦h₁ ⊗ₜ a⟧`
to `⟦h₁h⁻¹ ⊗ₜ a⟧`. -/
@[simps]
/--
Definition of `ind` / `ind` 的定义

English:
definition ind
  signature: : Representation k H (IndV φ ρ) where
  body: Coinvariants.map _ _ ⟨(MonoidAlgebra.mapDomainLinearMap k k fun x => x * h⁻¹).rTensor _,
    fun _ => by ext; simp [mul_assoc]⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [IndV, mul_assoc]

中文:
定义 ind
  签名: : Representation k H (IndV φ ρ) where
  定义体: Coinvariants.map _ _ ⟨(MonoidAlgebra.mapDomainLinearMap k k fun x => x * h⁻¹).rTensor _,
    fun _ => by ext; simp [mul_assoc]⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [IndV, mul_assoc]

Depends on / 依赖: Coinvariants, Coinvariants.map, MonoidAlgebra, MonoidAlgebra.mapDomainLinearMap, mapDomainLinearMap, map_mul, map_one, mul_assoc, rTensor
-/
noncomputable def ind : Representation k H (IndV φ ρ) where
  toFun h :=
    Coinvariants.map _ _ ⟨(MonoidAlgebra.mapDomainLinearMap k k fun x => x * h⁻¹).rTensor _,
    fun _ => by ext; simp [mul_assoc]⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [IndV, mul_assoc]

/--
lemma `ind_mk` / 引理 `ind_mk`

English:
lemma ind_mk
  given: (h₁ h₂ : H) (a : A)
  proof: by
  simp

中文:
引理 ind_mk
  条件: (h₁ h₂ : H) (a : A)
  证明: by
  simp
-/
lemma ind_mk (h₁ h₂ : H) (a : A) :
    ind φ ρ h₁ (IndV.mk _ _ h₂ a) = IndV.mk _ _ (h₂ * h₁⁻¹) a := by
  simp

end Representation

namespace Rep

open CategoryTheory Finsupp

variable {k : Type u} {G : Type v} {H : Type v'} [CommRing k] [Group G] [Group H] (φ : G ->* H)
  (A : Rep.{w} k G)

section Ind

/--
Definition of `ind` / `ind` 的定义

English:
abbreviation ind
  signature: : Rep k H
  body: Rep.of (A.ρ.ind φ)

中文:
缩写 ind
  签名: : Rep k H
  定义体: Rep.of (A.ρ.ind φ)

Depends on / 依赖: Rep.of
-/
noncomputable abbrev ind : Rep k H := Rep.of (A.ρ.ind φ)

/--
Definition of `indMap` / `indMap` 的定义

English:
definition indMap
  signature: {A B : Rep k G} (f : A ⟶ B)
  body: Rep.ofHom
  ⟨Representation.Coinvariants.map _ _ ⟨f.hom.toLinearMap.lTensor _, by
    simp [LinearMap.lTensor_comp_map, f.hom.2, LinearMap.map_comp_lTensor]⟩,
    fun g => by ext; simp⟩

中文:
定义 indMap
  签名: {A B : Rep k G} (f : A ⟶ B)
  定义体: Rep.ofHom
  ⟨Representation.Coinvariants.map _ _ ⟨f.hom.toLinearMap.lTensor _, by
    simp [LinearMap.lTensor_comp_map, f.hom.2, LinearMap.map_comp_lTensor]⟩,
    fun g => by ext; simp⟩

Depends on / 依赖: Rep.ofHom
-/
noncomputable def indMap {A B : Rep k G} (f : A ⟶ B) : ind φ A ⟶ ind φ B := Rep.ofHom
  ⟨Representation.Coinvariants.map _ _ ⟨f.hom.toLinearMap.lTensor _, by
    simp [LinearMap.lTensor_comp_map, f.hom.2, LinearMap.map_comp_lTensor]⟩,
    fun g => by ext; simp⟩

variable (k) in
/-- Given a group homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the induced `H`-representation `ind φ A`, with action on maps induced by left tensoring. -/
@[implicit_reducible, simps obj map]
/--
Definition of `indFunctor` / `indFunctor` 的定义

English:
definition indFunctor
  signature: : Rep.{w} k G ⥤ Rep k H where
  body: ind φ A
  map f := indMap φ f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

中文:
定义 indFunctor
  签名: : Rep.{w} k G ⥤ Rep k H where
  定义体: ind φ A
  map f := indMap φ f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl
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
/--
Definition of `indResHomEquiv` / `indResHomEquiv` 的定义

English:
definition indResHomEquiv
  signature: (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H)
  body: Rep.ofHom ⟨f.hom.toLinearMap ∘ₗ IndV.mk φ A.ρ 1, fun g => by
    ext x
    have := (hom_comm_apply f (φ g) (IndV.mk φ A.ρ 1 x)).symm
    simp_all [← Coinvariants.mk_inv_tmul] ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨Representation.Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => B.ρ h⁻¹ ∘ₗ f.hom.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
    fun g => by
      ext h x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [ofMulAction_single, mul_inv_rev, hom_comm_apply f g], fun g => by ext; simp⟩
  left_inv f := by
    ext h a
    simpa using (hom_comm_apply f h⁻¹ (IndV.mk φ A.ρ 1 a)).symm
  right_inv _ := by ext; simp

中文:
定义 indResHomEquiv
  签名: (A : Rep.{最大值 w v' u} k G) (B : Rep.{最大值 w v' u} k H)
  定义体: Rep.ofHom ⟨f.hom.toLinearMap ∘ₗ IndV.mk φ A.ρ 1, fun g => by
    ext x
    have := (hom_comm_apply f (φ g) (IndV.mk φ A.ρ 1 x)).symm
    simp_all [← Coinvariants.mk_inv_tmul] ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨Representation.Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => B.ρ h⁻¹ ∘ₗ f.hom.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
    fun g => by
      ext h x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [ofMulAction_single, mul_inv_rev, hom_comm_apply f g], fun g => by ext; simp⟩
  left_inv f := by
    ext h a
    simpa using (hom_comm_apply f h⁻¹ (IndV.mk φ A.ρ 1 a)).symm
  right_inv _ := by ext; simp

Depends on / 依赖: Coinvariants, Coinvariants.mk_inv_tmul, Finsupp, Finsupp.lift, Function, Function.comp_apply, IndV.mk, LinearMap, LinearMap.coe_comp, MonoidAlgebra, MonoidAlgebra.coeffLinearEquiv, MonoidAlgebra.lsingle_apply, Rep.ofHom, Representation, Representation.Coinvariants.lift, TensorProduct, TensorProduct.lift, coe_comp, coeffLinearEquiv, comp_apply
-/
noncomputable def indResHomEquiv (A : Rep.{max w v' u} k G) (B : Rep.{max w v' u} k H) :
    (ind φ A ⟶ B) ≃ₗ[k] (A ⟶ res φ B) where
  toFun f := Rep.ofHom ⟨f.hom.toLinearMap ∘ₗ IndV.mk φ A.ρ 1, fun g => by
    ext x
    have := (hom_comm_apply f (φ g) (IndV.mk φ A.ρ 1 x)).symm
    simp_all [← Coinvariants.mk_inv_tmul] ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨Representation.Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun h => B.ρ h⁻¹ ∘ₗ f.hom.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
    fun g => by
      ext h x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [ofMulAction_single, mul_inv_rev, hom_comm_apply f g], fun g => by ext; simp⟩
  left_inv f := by
    ext h a
    simpa using (hom_comm_apply f h⁻¹ (IndV.mk φ A.ρ 1 a)).symm
  right_inv _ := by ext; simp

variable (k) in
/--
Definition of `indResAdjunction` / `indResAdjunction` 的定义

English:
definition indResAdjunction
  signature: : indFunctor k φ ⊣ resFunctor.{max w v' u} φ
  body: Adjunction.mkOfHomEquiv {
    homEquiv A B := (indResHomEquiv φ A B).toEquiv
    homEquiv_naturality_left_symm _ _ := by
      change (indResHomEquiv φ _ _).symm (_ ≫ _) = _
      ext; simp [indMap, indResHomEquiv]
    homEquiv_naturality_right := by intros; rfl }

中文:
定义 indResAdjunction
  签名: : indFunctor k φ ⊣ resFunctor.{最大值 w v' u} φ
  定义体: Adjunction.mkOfHomEquiv {
    homEquiv A B := (indResHomEquiv φ A B).toEquiv
    homEquiv_naturality_left_symm _ _ := by
      change (indResHomEquiv φ _ _).symm (_ ≫ _) = _
      ext; simp [indMap, indResHomEquiv]
    homEquiv_naturality_right := by intros; rfl }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, indMap, indResHomEquiv, intros, mkOfHomEquiv, toEquiv
-/
noncomputable def indResAdjunction : indFunctor k φ ⊣ resFunctor.{max w v' u} φ :=
  Adjunction.mkOfHomEquiv {
    homEquiv A B := (indResHomEquiv φ A B).toEquiv
    homEquiv_naturality_left_symm _ _ := by
      change (indResHomEquiv φ _ _).symm (_ ≫ _) = _
      ext; simp [indMap, indResHomEquiv]
    homEquiv_naturality_right := by intros; rfl }

open Finsupp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (indFunctor.{max u v' w} k φ).IsLeftAdjoint
  body: (indResAdjunction k φ).isLeftAdjoint

中文:
实例 :
  签名: (indFunctor.{最大值 u v' w} k φ).是左伴随
  定义体: (indResAdjunction k φ).isLeftAdjoint

Depends on / 依赖: indResAdjunction, isLeftAdjoint
-/
noncomputable instance : (indFunctor.{max u v' w} k φ).IsLeftAdjoint :=
  (indResAdjunction k φ).isLeftAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (resFunctor.{max u v' w} (k := k) φ).IsRightAdjoint
  body: (indResAdjunction k φ).isRightAdjoint

中文:
实例 :
  签名: (resFunctor.{最大值 u v' w} (k := k) φ).是右伴随
  定义体: (indResAdjunction k φ).isRightAdjoint

Depends on / 依赖: IsRightAdjoint
-/
noncomputable instance : (resFunctor.{max u v' w} (k := k) φ).IsRightAdjoint :=
  (indResAdjunction k φ).isRightAdjoint

end Adjunction

section

variable {G H : Type u} [Group G] [Group H] (φ : G ->* H) (A : Rep k G) (B : Rep k H)

open Representation

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coinvariantsTensorIndHom` / `coinvariantsTensorIndHom` 的定义

English:
definition coinvariantsTensorIndHom
  signature: :
  body: ModuleCat.ofHom Coinvariants.lift _ (TensorProduct.lift <| Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ <| fun g =>
      (coinvariantsTensorMk A (res φ B)).compl₂ (B.ρ g)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
      fun g => by ext; simpa [coinvariantsTensorMk, Coinvariants.mk_eq_iff]
        using! Coinvariants.sub_mem_ker _ _) fun _ => by
    simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V, tensor_ρ, res_obj_ρ,
      Functor.postcompose₂_obj_obj_obj_obj, coinvariantsFunctor_obj_carrier,
      tprod_apply, ind_apply]
    ext; simp

中文:
定义 coinvariantsTensorIndHom
  签名: :
  定义体: ModuleCat.ofHom Coinvariants.lift _ (TensorProduct.lift <| Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ <| fun g =>
      (coinvariantsTensorMk A (res φ B)).compl₂ (B.ρ g)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
      fun g => by ext; simpa [coinvariantsTensorMk, Coinvariants.mk_eq_iff]
        using! Coinvariants.sub_mem_ker _ _) fun _ => by
    simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V, tensor_ρ, res_obj_ρ,
      Functor.postcompose₂_obj_obj_obj_obj, coinvariantsFunctor_obj_carrier,
      tprod_apply, ind_apply]
    ext; simp

Depends on / 依赖: Coinvariants, Coinvariants.lift, Coinvariants.mk_eq_iff, Coinvariants.sub_mem_ker, Finsupp, Finsupp.lift, Functor, Functor.postcompose, ModuleCat, ModuleCat.ofHom, MonoidAlgebra, MonoidAlgebra.coeffLinearEquiv, MonoidalCategory, MonoidalCategory.curriedTensor_obj_obj, TensorProduct, TensorProduct.lift, coeffLinearEquiv, coinvariantsFunctor_obj_c, coinvariantsTensorMk, curriedTensor_obj_obj
-/
noncomputable def coinvariantsTensorIndHom :
    ((coinvariantsTensor k H).obj (ind φ A)).obj B ⟶
      ((coinvariantsTensor k G).obj A).obj (res φ B) :=
ModuleCat.ofHom Coinvariants.lift _ (TensorProduct.lift <| Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ <| fun g =>
      (coinvariantsTensorMk A (res φ B)).compl₂ (B.ρ g)) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
      fun g => by ext; simpa [coinvariantsTensorMk, Coinvariants.mk_eq_iff]
        using! Coinvariants.sub_mem_ker _ _) fun _ => by
    simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V, tensor_ρ, res_obj_ρ,
      Functor.postcompose₂_obj_obj_obj_obj, coinvariantsFunctor_obj_carrier,
      tprod_apply, ind_apply]
    ext; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {A B} in
/--
lemma `coinvariantsTensorIndHom_mk_tmul_indVMk` / 引理 `coinvariantsTensorIndHom_mk_tmul_indVMk`

English:
lemma coinvariantsTensorIndHom_mk_tmul_indVMk
  given: (h : H) (x : A) (y : B)
  proof: by
  simp [coinvariantsTensorIndHom, coinvariantsTensorMk]

中文:
引理 coinvariantsTensorIndHom_mk_tmul_indVMk
  条件: (h : H) (x : A) (y : B)
  证明: by
  simp [coinvariantsTensorIndHom, coinvariantsTensorMk]

Depends on / 依赖: coinvariantsTensorIndHom, coinvariantsTensorMk
-/
lemma coinvariantsTensorIndHom_mk_tmul_indVMk (h : H) (x : A) (y : B) :
    coinvariantsTensorIndHom φ A B (coinvariantsTensorMk _ _ (IndV.mk φ _ h x) y) =
      coinvariantsTensorMk _ _ x (B.ρ h y) := by
  simp [coinvariantsTensorIndHom, coinvariantsTensorMk]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coinvariantsTensorIndInv` / `coinvariantsTensorIndInv` 的定义

English:
definition coinvariantsTensorIndInv
  signature: :
  body: ModuleCat.ofHom Coinvariants.lift _ (TensorProduct.lift <|
    (coinvariantsTensorMk (ind (k := k) φ A) B) ∘ₗ IndV.mk _ _ 1) fun s => by
    simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V, tensor_ρ, tprod_apply,
      MonoidHom.coe_comp, Function.comp_apply]
    ext x y
    simpa [Coinvariants.mk_eq_iff, coinvariantsTensorMk] using
Coinvariants.mem_ker_of_eq (φ s) (IndV.mk φ A.ρ (1 : H) x otimesₜ[k] y) _ by
      simp [← Coinvariants.mk_inv_tmul]

中文:
定义 coinvariantsTensorIndInv
  签名: :
  定义体: ModuleCat.ofHom Coinvariants.lift _ (TensorProduct.lift <|
    (coinvariantsTensorMk (ind (k := k) φ A) B) ∘ₗ IndV.mk _ _ 1) fun s => by
    simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V, tensor_ρ, tprod_apply,
      MonoidHom.coe_comp, Function.comp_apply]
    ext x y
    simpa [Coinvariants.mk_eq_iff, coinvariantsTensorMk] using
Coinvariants.mem_ker_of_eq (φ s) (IndV.mk φ A.ρ (1 : H) x otimesₜ[k] y) _ by
      simp [← Coinvariants.mk_inv_tmul]

Depends on / 依赖: Coinvariants, Coinvariants.lift, Coinvariants.mem_ker_of_eq, Coinvariants.mk_eq_iff, Coinvariants.mk_inv_tmul, Function, Function.comp_apply, IndV.mk, ModuleCat, ModuleCat.ofHom, MonoidHom, MonoidHom.coe_comp, MonoidalCategory, MonoidalCategory.curriedTensor_obj_obj, TensorProduct, TensorProduct.lift, coe_comp, coinvariantsTensorMk, comp_apply, curriedTensor_obj_obj
-/
noncomputable def coinvariantsTensorIndInv :
    ((coinvariantsTensor k G).obj A).obj (res φ B) ⟶
      ((coinvariantsTensor k H).obj (ind φ A)).obj B :=
ModuleCat.ofHom Coinvariants.lift _ (TensorProduct.lift <|
    (coinvariantsTensorMk (ind (k := k) φ A) B) ∘ₗ IndV.mk _ _ 1) fun s => by
    simp only [MonoidalCategory.curriedTensor_obj_obj, tensor_V, tensor_ρ, tprod_apply,
      MonoidHom.coe_comp, Function.comp_apply]
    ext x y
    simpa [Coinvariants.mk_eq_iff, coinvariantsTensorMk] using
Coinvariants.mem_ker_of_eq (φ s) (IndV.mk φ A.ρ (1 : H) x otimesₜ[k] y) _ by
      simp [← Coinvariants.mk_inv_tmul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {A B} in
/--
lemma `coinvariantsTensorIndInv_mk_tmul_indMk` / 引理 `coinvariantsTensorIndInv_mk_tmul_indMk`

English:
lemma coinvariantsTensorIndInv_mk_tmul_indMk
  given: (x : A) (y : B)
  proof: by
  simp [coinvariantsTensorIndInv, coinvariantsTensorMk]

中文:
引理 coinvariantsTensorIndInv_mk_tmul_indMk
  条件: (x : A) (y : B)
  证明: by
  simp [coinvariantsTensorIndInv, coinvariantsTensorMk]

Depends on / 依赖: coinvariantsTensorIndInv, coinvariantsTensorMk
-/
lemma coinvariantsTensorIndInv_mk_tmul_indMk (x : A) (y : B) :
    coinvariantsTensorIndInv φ A B (Coinvariants.mk
(A.ρ.tprod (Rep.ρ (res φ B))) x otimesₜ y) =
      coinvariantsTensorMk _ _ (IndV.mk φ _ 1 x) y := by
  simp [coinvariantsTensorIndInv, coinvariantsTensorMk]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H`, `A : Rep k G` and `B : Rep k H`, this is the `k`-linear
isomorphism `(Ind(φ)(A) ⊗ B))_H ⟶ (A ⊗ Res(φ)(B))_G` sending `⟦h ⊗ₜ a⟧ ⊗ₜ b` to `⟦a ⊗ ρ(h)(b)⟧`
for all `h : H`, `a : A`, and `b : B`. -/
@[simps]
/--
Definition of `coinvariantsTensorIndIso` / `coinvariantsTensorIndIso` 的定义

English:
definition coinvariantsTensorIndIso
  signature: :
  body: coinvariantsTensorIndHom φ A B
  inv := coinvariantsTensorIndInv φ A B
  hom_inv_id := by
    ext h a b
    simpa [coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom, Coinvariants.mk_eq_iff] using
Coinvariants.mem_ker_of_eq h (IndV.mk φ _ h a otimesₜ[k] b) _ by simp
  inv_hom_id := by
    ext
    simp [coinvariantsTensorIndInv, coinvariantsTensorMk, coinvariantsTensorIndHom]

中文:
定义 coinvariantsTensorIndIso
  签名: :
  定义体: coinvariantsTensorIndHom φ A B
  inv := coinvariantsTensorIndInv φ A B
  hom_inv_id := by
    ext h a b
    simpa [coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom, Coinvariants.mk_eq_iff] using
Coinvariants.mem_ker_of_eq h (IndV.mk φ _ h a otimesₜ[k] b) _ by simp
  inv_hom_id := by
    ext
    simp [coinvariantsTensorIndInv, coinvariantsTensorMk, coinvariantsTensorIndHom]

Depends on / 依赖: coinvariantsTensorIndHom
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
Coinvariants.mem_ker_of_eq h (IndV.mk φ _ h a otimesₜ[k] b) _ by simp
  inv_hom_id := by
    ext
    simp [coinvariantsTensorIndInv, coinvariantsTensorMk, coinvariantsTensorIndHom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a group hom `φ : G →* H` and `A : Rep k G`, the functor `Rep k H ⥤ ModuleCat k` sending
`B ↦ (Ind(φ)(A) ⊗ B))_H` is naturally isomorphic to the one sending `B ↦ (A ⊗ Res(φ)(B))_G`. -/
@[simps! hom_app inv_app]
/--
Definition of `coinvariantsTensorIndNatIso` / `coinvariantsTensorIndNatIso` 的定义

English:
definition coinvariantsTensorIndNatIso
  signature: :
  body: NatIso.ofComponents (fun B => coinvariantsTensorIndIso φ A B) fun {X Y} f => by
    ext
    simp [coinvariantsTensorIndHom, coinvariantsTensorMk, hom_comm_apply]

中文:
定义 coinvariantsTensorInd自然数Iso
  签名: :
  定义体: NatIso.ofComponents (fun B => coinvariantsTensorIndIso φ A B) fun {X Y} f => by
    ext
    simp [coinvariantsTensorIndHom, coinvariantsTensorMk, hom_comm_apply]

Depends on / 依赖: NatIso, NatIso.ofComponents, coinvariantsTensorIndHom, coinvariantsTensorIndIso, coinvariantsTensorMk, hom_comm_apply, ofComponents
-/
noncomputable def coinvariantsTensorIndNatIso :
    (coinvariantsTensor k H).obj (ind φ A) ≅ resFunctor φ ⋙ (coinvariantsTensor k G).obj A :=
  NatIso.ofComponents (fun B => coinvariantsTensorIndIso φ A B) fun {X Y} f => by
    ext
    simp [coinvariantsTensorIndHom, coinvariantsTensorMk, hom_comm_apply]

end
end Rep
