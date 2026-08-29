/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Character module of a module

For commutative ring `R` and an `R`-module `M` and an injective module `D`, its character module
`M⋆` is defined to be `R`-linear maps `M ⟶ D`.

`M⋆` also has an `R`-module structure given by `(r • f) m = f (r • m)`.

## Main results

- `CharacterModuleFunctor` : the contravariant functor of `R`-modules where `M ↦ M⋆` and
  an `R`-linear map `l : M ⟶ N` induces an `R`-linear map `l⋆ : f ↦ f ∘ l` where `f : N⋆`.
- `LinearMap.dual_surjective_of_injective` : If `l` is injective then `l⋆` is surjective,
  in another word taking character module as a functor sends monos to epis.
- `CharacterModule.homEquiv` : there is a bijection between linear map `Hom(N, M⋆)` and
  `(N ⊗ M)⋆` given by `curry` and `uncurry`.

-/

@[expose] public section

open CategoryTheory

universe uR uA uB

variable (R : Type uR) [CommRing R]
variable (A : Type uA) [AddCommGroup A]
variable (A' : Type*) [AddCommGroup A']
variable (B : Type uB) [AddCommGroup B]

/--
Definition of `CharacterModule` / `CharacterModule` 的定义

English:
definition CharacterModule
  signature: : Type uA
  body: A ->+ AddCircle (1 : Rat)

中文:
定义 CharacterModule
  签名: : 类型uA
  定义体: A ->+ AddCircle (1 : Rat)

Depends on / 依赖: AddCircle
-/
def CharacterModule : Type uA := A ->+ AddCircle (1 : Rat)

namespace CharacterModule

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (CharacterModule A) A (AddCircle (1 : Rat))
  body: c.toFun
  coe_injective _ _ _ := by simp_all

中文:
实例 :
  签名: 函数状 (CharacterModule A) A (AddCircle (1 : 有理数))
  定义体: c.toFun
  coe_injective _ _ _ := by simp_all

Depends on / 依赖: c.toFun
-/
instance : FunLike (CharacterModule A) A (AddCircle (1 : Rat)) where
  coe c := c.toFun
  coe_injective _ _ _ := by simp_all

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearMapClass (CharacterModule A) Int A (AddCircle (1 : Rat))
  body: AddMonoidHom.map_add
  map_smulₛₗ := AddMonoidHom.map_zsmul

中文:
实例 :
  签名: 线性映射类 (CharacterModule A) 整数 A (AddCircle (1 : 有理数))
  定义体: AddMonoidHom.map_add
  map_smulₛₗ := AddMonoidHom.map_zsmul

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_add, map_add
-/
instance : LinearMapClass (CharacterModule A) Int A (AddCircle (1 : Rat)) where
  map_add := AddMonoidHom.map_add
  map_smulₛₗ := AddMonoidHom.map_zsmul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (CharacterModule A)
  body: inferInstanceAs (AddCommGroup (A ->+ _))

中文:
实例 :
  签名: 加法交换群 (CharacterModule A)
  定义体: inferInstanceAs (AddCommGroup (A ->+ _))

Depends on / 依赖: AddCommGroup
-/
instance : AddCommGroup (CharacterModule A) :=
  inferInstanceAs (AddCommGroup (A ->+ _))

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {c c' : CharacterModule A} (h : forall x, c x = c' x)
  statement: c = c'
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {c c' : CharacterModule A} (h : 对任意 x, c x = c' x)
  结论: c = c'
  证明: DFunLike.ext _ _ h
-/
@[ext] theorem ext {c c' : CharacterModule A} (h : forall x, c x = c' x) : c = c' := DFunLike.ext _ _ h

section module

variable [Module R A] [Module R A'] [Module R B]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (CharacterModule A)
  body: fast_instance% Module.compHom (A ->+ _) (RingEquiv.toOpposite _ |>.toRingHom : R ->+* Rᵈᵐᵃ)

中文:
实例 :
  签名: 模 R (CharacterModule A)
  定义体: fast_instance% Module.compHom (A ->+ _) (RingEquiv.toOpposite _ |>.toRingHom : R ->+* Rᵈᵐᵃ)

Depends on / 依赖: Module, Module.compHom, RingEquiv, RingEquiv.toOpposite, compHom, fast_instance, toOpposite, toRingHom
-/
instance : Module R (CharacterModule A) :=
  fast_instance% Module.compHom (A ->+ _) (RingEquiv.toOpposite _ |>.toRingHom : R ->+* Rᵈᵐᵃ)

variable {R A B}

/--
lemma `smul_apply` / 引理 `smul_apply`

English:
lemma smul_apply
  given: (c : CharacterModule A) (r : R) (a : A)
  statement: (r • c) a = c (r • a)
  proof: rfl

中文:
引理 smul_apply
  条件: (c : CharacterModule A) (r : R) (a : A)
  结论: (r • c) a = c (r • a)
  证明: rfl
-/
@[simp] lemma smul_apply (c : CharacterModule A) (r : R) (a : A) : (r • c) a = c (r • a) := rfl

/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: (f : A ->ₗ[R] B)
  body: L.comp f.toAddMonoidHom
  map_add' := by aesop
  map_smul' r c := by ext x; exact congr(c $(f.map_smul r x)).symm

@[simp]

中文:
定义 dual
  签名: (f : A ->ₗ[R] B)
  定义体: L.comp f.toAddMonoidHom
  map_add' := by aesop
  map_smul' r c := by ext x; exact congr(c $(f.map_smul r x)).symm

@[simp]
-/
@[simps] def dual (f : A ->ₗ[R] B) : CharacterModule B ->ₗ[R] CharacterModule A where
  toFun L := L.comp f.toAddMonoidHom
  map_add' := by aesop
  map_smul' r c := by ext x; exact congr(c $(f.map_smul r x)).symm

@[simp]
/--
lemma `dual_zero` / 引理 `dual_zero`

English:
lemma dual_zero
  statement: dual (0 : A ->ₗ[R] B) = 0
  proof: by
  ext f
  exact map_zero f

中文:
引理 dual_zero
  结论: dual (0 : A ->ₗ[R] B) = 0
  证明: by
  ext f
  exact map_zero f

Depends on / 依赖: map_zero
-/
lemma dual_zero : dual (0 : A ->ₗ[R] B) = 0 := by
  ext f
  exact map_zero f

/--
lemma `dual_comp` / 引理 `dual_comp`

English:
lemma dual_comp
  given: {C : Type*} [AddCommGroup C] [Module R C] (f : A ->ₗ[R] B) (g : B ->ₗ[R] C)
  proof: by
  ext
  rfl

中文:
引理 dual_comp
  条件: {C : 类型} [加法交换群 C] [模 R C] (f : A ->ₗ[R] B) (g : B ->ₗ[R] C)
  证明: by
  ext
  rfl
-/
lemma dual_comp {C : Type*} [AddCommGroup C] [Module R C] (f : A ->ₗ[R] B) (g : B ->ₗ[R] C) :
    dual (g.comp f) = (dual f).comp (dual g) := by
  ext
  rfl

/--
lemma `dual_injective_of_surjective` / 引理 `dual_injective_of_surjective`

English:
lemma dual_injective_of_surjective
  given: (f : A ->ₗ[R] B) (hf : Function.Surjective f)
  proof: by
  intro φ ψ eq
  ext x
  obtain ⟨y, rfl⟩ := hf x
  change (dual f) φ _ = (dual f) ψ _
  rw [eq]

中文:
引理 dual_injective_of_surjective
  条件: (f : A ->ₗ[R] B) (hf : 函数.满射 f)
  证明: by
  intro φ ψ eq
  ext x
  obtain ⟨y, rfl⟩ := hf x
  change (dual f) φ _ = (dual f) ψ _
  rw [eq]
-/
lemma dual_injective_of_surjective (f : A ->ₗ[R] B) (hf : Function.Surjective f) :
    Function.Injective (dual f) := by
  intro φ ψ eq
  ext x
  obtain ⟨y, rfl⟩ := hf x
  change (dual f) φ _ = (dual f) ψ _
  rw [eq]

/--
lemma `dual_surjective_of_injective` / 引理 `dual_surjective_of_injective`

English:
lemma dual_surjective_of_injective
  given: (f : A ->ₗ[R] B) (hf : Function.Injective f)
  proof: (Module.Baer.of_divisible _).extension_property_addMonoidHom _ hf

中文:
引理 dual_surjective_of_injective
  条件: (f : A ->ₗ[R] B) (hf : 函数.单射 f)
  证明: (Module.Baer.of_divisible _).extension_property_addMonoidHom _ hf

Depends on / 依赖: Module, Module.Baer.of_divisible, extension_property_addMonoidHom, of_divisible
-/
lemma dual_surjective_of_injective (f : A ->ₗ[R] B) (hf : Function.Injective f) :
    Function.Surjective (dual f) :=
  (Module.Baer.of_divisible _).extension_property_addMonoidHom _ hf

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (e : A ≃ₗ[R] B)
  body: .ofLinearMap (dual e.symm) (dual e)
    (by ext c _; exact congr(c $(e.right_inv _)))
    (by ext c _; exact congr(c $(e.left_inv _)))

中文:
定义 congr
  签名: (e : A ≃ₗ[R] B)
  定义体: .ofLinearMap (dual e.symm) (dual e)
    (by ext c _; exact congr(c $(e.right_inv _)))
    (by ext c _; exact congr(c $(e.left_inv _)))

Depends on / 依赖: e.left_inv, e.right_inv, e.symm, left_inv, ofLinearMap, right_inv
-/
def congr (e : A ≃ₗ[R] B) : CharacterModule A ≃ₗ[R] CharacterModule B :=
  .ofLinearMap (dual e.symm) (dual e)
    (by ext c _; exact congr(c $(e.right_inv _)))
    (by ext c _; exact congr(c $(e.left_inv _)))

open TensorProduct

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `uncurry` / `uncurry` 的定义

English:
definition uncurry
  signature: :
  body: TensorProduct.liftAddHom c.toAddMonoidHom fun r a b => congr($(c.map_smul r a) b)
  map_add' c c' := DFunLike.ext _ _ fun x => by refine x.induction_on ?_ ?_ ?_ <;> aesop
  map_smul' r c := DFunLike.ext _ _ fun x => x.induction_on
    (by simp_rw [map_zero]) (fun a b => congr($(c.map_smul r a) b).sy

中文:
定义 uncurry
  签名: :
  定义体: TensorProduct.liftAddHom c.toAddMonoidHom fun r a b => congr($(c.map_smul r a) b)
  map_add' c c' := DFunLike.ext _ _ fun x => by refine x.induction_on ?_ ?_ ?_ <;> aesop
  map_smul' r c := DFunLike.ext _ _ fun x => x.induction_on
    (by simp_rw [map_zero]) (fun a b => congr($(c.map_smul r a) b).sy
-/
@[simps] noncomputable def uncurry :
    (A ->ₗ[R] CharacterModule B) ->ₗ[R] CharacterModule (A otimes[R] B) where
  toFun c := TensorProduct.liftAddHom c.toAddMonoidHom fun r a b => congr($(c.map_smul r a) b)
  map_add' c c' := DFunLike.ext _ _ fun x => by refine x.induction_on ?_ ?_ ?_ <;> aesop
  map_smul' r c := DFunLike.ext _ _ fun x => x.induction_on
    (by simp_rw [map_zero]) (fun a b => congr($(c.map_smul r a) b).symm) (by aesop)

/--
Definition of `curry` / `curry` 的定义

English:
definition curry
  signature: :
  body: { toFun := (c.comp <| TensorProduct.mk R A B ·)
    map_add' := fun _ _ => DFunLike.ext _ _ fun b =>
      congr(c <| $(map_add (mk R A B) _ _) b).trans (c.map_add _ _)
    map_smul' := fun r a => by ext; exact congr(c $(TensorProduct.tmul_smul _ _ _)).symm }
  map_add' _ _ := rfl
  map_smul' r c :=

中文:
定义 curry
  签名: :
  定义体: { toFun := (c.comp <| TensorProduct.mk R A B ·)
    map_add' := fun _ _ => DFunLike.ext _ _ fun b =>
      congr(c <| $(map_add (mk R A B) _ _) b).trans (c.map_add _ _)
    map_smul' := fun r a => by ext; exact congr(c $(TensorProduct.tmul_smul _ _ _)).symm }
  map_add' _ _ := rfl
  map_smul' r c :=
-/
@[simps] noncomputable def curry :
    CharacterModule (A otimes[R] B) ->ₗ[R] (A ->ₗ[R] CharacterModule B) where
  toFun c :=
  { toFun := (c.comp <| TensorProduct.mk R A B ·)
    map_add' := fun _ _ => DFunLike.ext _ _ fun b =>
      congr(c <| $(map_add (mk R A B) _ _) b).trans (c.map_add _ _)
    map_smul' := fun r a => by ext; exact congr(c $(TensorProduct.tmul_smul _ _ _)).symm }
  map_add' _ _ := rfl
  map_smul' r c := by ext; exact congr(c $(TensorProduct.tmul_smul _ _ _)).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: :
  body: .ofLinearMap uncurry curry (by ext _ z; refine z.induction_on ?_ ?_ ?_ <;> aesop) (by aesop)

中文:
定义 homEquiv
  签名: :
  定义体: .ofLinearMap uncurry curry (by ext _ z; refine z.induction_on ?_ ?_ ?_ <;> aesop) (by aesop)
-/
@[simps!] noncomputable def homEquiv :
    (A ->ₗ[R] CharacterModule B) ≃ₗ[R] CharacterModule (A otimes[R] B) :=
  .ofLinearMap uncurry curry (by ext _ z; refine z.induction_on ?_ ?_ ?_ <;> aesop) (by aesop)

/--
theorem `dual_rTensor_conj_homEquiv` / 定理 `dual_rTensor_conj_homEquiv`

English:
theorem dual_rTensor_conj_homEquiv
  given: (f : A ->ₗ[R] A')
  proof: rfl

中文:
定理 dual_rTensor_conj_homEquiv
  条件: (f : A ->ₗ[R] A')
  证明: rfl
-/
theorem dual_rTensor_conj_homEquiv (f : A ->ₗ[R] A') :
    homEquiv.symm.toLinearMap ∘ₗ dual (f.rTensor B) ∘ₗ homEquiv.toLinearMap = f.lcomp R _ := rfl

end module

/--
Definition of `int` / `int` 的定义

English:
abbreviation int
  signature: : Type
  body: CharacterModule Int

中文:
缩写 int
  签名: : 类型
  定义体: CharacterModule Int
-/
protected abbrev int : Type := CharacterModule Int

/--
Definition of `int.divByNat` / `int.divByNat` 的定义

English:
abbreviation int.divByNat
  signature: (n : Nat)
  body: .toAddMonoidHom LinearMap.toSpanSingleton Int _ (QuotientAddGroup.mk (n : Rat)⁻¹)

中文:
缩写 int.divBy自然数
  签名: (n : 自然数)
  定义体: .toAddMonoidHom LinearMap.toSpanSingleton Int _ (QuotientAddGroup.mk (n : Rat)⁻¹)
-/
protected abbrev int.divByNat (n : Nat) : CharacterModule.int :=
.toAddMonoidHom LinearMap.toSpanSingleton Int _ (QuotientAddGroup.mk (n : Rat)⁻¹)

/--
lemma `int.divByNat_self` / 引理 `int.divByNat_self`

English:
lemma int.divByNat_self
  given: (n : Nat)
  proof: by
  obtain rfl | h0 := eq_or_ne n 0
  · apply map_zero
  exact (AddCircle.coe_eq_zero_iff _).mpr
    ⟨1, by simp [mul_inv_cancel₀ (Nat.cast_ne_zero (R := Rat).mpr h0)]⟩

中文:
引理 int.divBy自然数_self
  条件: (n : 自然数)
  证明: by
  obtain rfl | h0 := eq_or_ne n 0
  · apply map_zero
  exact (AddCircle.coe_eq_zero_iff _).mpr
    ⟨1, by simp [mul_inv_cancel₀ (Nat.cast_ne_zero (R := Rat).mpr h0)]⟩
-/
protected lemma int.divByNat_self (n : Nat) :
    int.divByNat n n = 0 := by
  obtain rfl | h0 := eq_or_ne n 0
  · apply map_zero
  exact (AddCircle.coe_eq_zero_iff _).mpr
    ⟨1, by simp [mul_inv_cancel₀ (Nat.cast_ne_zero (R := Rat).mpr h0)]⟩

variable {A}

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `intSpanEquivQuotAddOrderOf` / `intSpanEquivQuotAddOrderOf` 的定义

English:
definition intSpanEquivQuotAddOrderOf
  signature: (a : A)
  body: LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range Int A a) ≪≫ₗ
  (LinearMap.quotKerEquivRange <| LinearMap.toSpanSingleton Int A a).symm ≪≫ₗ
  Submodule.quotEquivOfEq _ _ (by
    ext1 x
    rw [Ideal.mem_span_singleton]; rw [addOrderOf_dvd_iff_zsmul_eq_zero]; rw [LinearMap.mem_ker]; rw [Linear

中文:
定义 intSpanEquivQuotAddOrderOf
  签名: (a : A)
  定义体: LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range Int A a) ≪≫ₗ
  (LinearMap.quotKerEquivRange <| LinearMap.toSpanSingleton Int A a).symm ≪≫ₗ
  Submodule.quotEquivOfEq _ _ (by
    ext1 x
    rw [Ideal.mem_span_singleton]; rw [addOrderOf_dvd_iff_zsmul_eq_zero]; rw [LinearMap.mem_ker]; rw [Linear
-/
@[simps!] noncomputable def intSpanEquivQuotAddOrderOf (a : A) :
    (Int ∙ a) ≃ₗ[Int] Int ⧸ Ideal.span {(addOrderOf a : Int)} :=
  LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range Int A a) ≪≫ₗ
  (LinearMap.quotKerEquivRange <| LinearMap.toSpanSingleton Int A a).symm ≪≫ₗ
  Submodule.quotEquivOfEq _ _ (by
    ext1 x
    rw [Ideal.mem_span_singleton]; rw [addOrderOf_dvd_iff_zsmul_eq_zero]; rw [LinearMap.mem_ker]; rw [LinearMap.toSpanSingleton_apply])

/--
lemma `intSpanEquivQuotAddOrderOf_apply_self` / 引理 `intSpanEquivQuotAddOrderOf_apply_self`

English:
lemma intSpanEquivQuotAddOrderOf_apply_self
  given: (a : A)
  proof: (LinearEquiv.eq_symm_apply _).mp Subtype.ext (one_zsmul _).symm

中文:
引理 intSpanEquivQuotAddOrderOf_apply_self
  条件: (a : A)
  证明: (LinearEquiv.eq_symm_apply _).mp Subtype.ext (one_zsmul _).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.eq_symm_apply, Subtype, Subtype.ext, eq_symm_apply, one_zsmul
-/
lemma intSpanEquivQuotAddOrderOf_apply_self (a : A) :
    intSpanEquivQuotAddOrderOf a ⟨a, Submodule.mem_span_singleton_self a⟩ =
    Submodule.Quotient.mk 1 :=
(LinearEquiv.eq_symm_apply _).mp Subtype.ext (one_zsmul _).symm

/--
Definition of `ofSpanSingleton` / `ofSpanSingleton` 的定义

English:
definition ofSpanSingleton
  signature: (a : A)
  body: let l : Int ⧸ Ideal.span {(addOrderOf a : Int)} ->ₗ[Int] AddCircle (1 : Rat) :=
    Submodule.liftQSpanSingleton _
      (CharacterModule.int.divByNat <|
        if addOrderOf a = 0 then 2 else addOrderOf a).toIntLinearMap <| by
        split_ifs with h
        · rw [h, Nat.cast_zero, map_zero]
    

中文:
定义 ofSpanSingleton
  签名: (a : A)
  定义体: let l : Int ⧸ Ideal.span {(addOrderOf a : Int)} ->ₗ[Int] AddCircle (1 : Rat) :=
    Submodule.liftQSpanSingleton _
      (CharacterModule.int.divByNat <|
        if addOrderOf a = 0 then 2 else addOrderOf a).toIntLinearMap <| by
        split_ifs with h
        · rw [h, Nat.cast_zero, map_zero]
    

Depends on / 依赖: AddCircle, CharacterModule, CharacterModule.int.divByNat, CharacterModule.int.divByNat_self, Ideal.span, Nat.cast_zero, Submodule, Submodule.liftQSpanSingleton, addOrderOf, cast_zero, divByNat, divByNat_self, intSpanEquivQuotAddOrderOf, liftQSpanSingleton, map_zero, split_ifs, toAddMonoidHom, toIntLinearMap
-/
noncomputable def ofSpanSingleton (a : A) : CharacterModule (Int ∙ a) :=
  let l : Int ⧸ Ideal.span {(addOrderOf a : Int)} ->ₗ[Int] AddCircle (1 : Rat) :=
    Submodule.liftQSpanSingleton _
      (CharacterModule.int.divByNat <|
        if addOrderOf a = 0 then 2 else addOrderOf a).toIntLinearMap <| by
        split_ifs with h
        · rw [h, Nat.cast_zero, map_zero]
        · apply CharacterModule.int.divByNat_self
.toAddMonoidHom l ∘ₗ intSpanEquivQuotAddOrderOf a

/--
lemma `eq_zero_of_ofSpanSingleton_apply_self` / 引理 `eq_zero_of_ofSpanSingleton_apply_self`

English:
lemma eq_zero_of_ofSpanSingleton_apply_self
  statement: (a : A)
  proof: by
  erw [ofSpanSingleton, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
     intSpanEquivQuotAddOrderOf_apply_self, Submodule.liftQSpanSingleton_apply,
    AddMonoidHom.coe_toIntLinearMap, int.divByNat, LinearMap.toSpanSingleton_apply_one,
    AddCircle.coe_eq_zero_iff] at h
  rcases h with ⟨

中文:
引理 eq_zero_of_ofSpanSingleton_apply_self
  结论: (a : A)
  证明: by
  erw [ofSpanSingleton, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
     intSpanEquivQuotAddOrderOf_apply_self, Submodule.liftQSpanSingleton_apply,
    AddMonoidHom.coe_toIntLinearMap, int.divByNat, LinearMap.toSpanSingleton_apply_one,
    AddCircle.coe_eq_zero_iff] at h
  rcases h with ⟨

Depends on / 依赖: AddCircle, AddCircle.coe_eq_zero_iff, AddMonoid, AddMonoid.addOrderOf_eq_one_iff, AddMonoidHom, AddMonoidHom.coe_toIntLinearMap, LinearMap, LinearMap.comp_apply, LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply_one, Rat.den, Rat.den_intCast, Rat.inv_natCast_den_of_pos, Submodule, Submodule.liftQSpanSingleton_apply, addOrderOf_eq_one_iff, apply_fun, coe_eq_zero_iff, coe_toIntLinearMap, comp_apply
-/
lemma eq_zero_of_ofSpanSingleton_apply_self (a : A)
    (h : ofSpanSingleton a ⟨a, Submodule.mem_span_singleton_self a⟩ = 0) : a = 0 := by
  erw [ofSpanSingleton, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply,
     intSpanEquivQuotAddOrderOf_apply_self, Submodule.liftQSpanSingleton_apply,
    AddMonoidHom.coe_toIntLinearMap, int.divByNat, LinearMap.toSpanSingleton_apply_one,
    AddCircle.coe_eq_zero_iff] at h
  rcases h with ⟨n, hn⟩
  apply_fun Rat.den at hn
  rw [zsmul_one]; rw [Rat.den_intCast]; rw [Rat.inv_natCast_den_of_pos] at hn
  · split_ifs at hn
    · cases hn
    · rwa [eq_comm, AddMonoid.addOrderOf_eq_one_iff] at hn
  · grind

/--
lemma `exists_character_apply_ne_zero_of_ne_zero` / 引理 `exists_character_apply_ne_zero_of_ne_zero`

English:
lemma exists_character_apply_ne_zero_of_ne_zero
  given: {a : A} (ne_zero : a != 0)
  proof: have ⟨c, hc⟩ := dual_surjective_of_injective _ (Submodule.injective_subtype _) (ofSpanSingleton a)
⟨c, fun h => ne_zero eq_zero_of_ofSpanSingleton_apply_self a by rwa [← hc]⟩

中文:
引理 存在_character_apply_ne_zero_of_ne_zero
  条件: {a : A} (ne_zero : a != 0)
  证明: have ⟨c, hc⟩ := dual_surjective_of_injective _ (Submodule.injective_subtype _) (ofSpanSingleton a)
⟨c, fun h => ne_zero eq_zero_of_ofSpanSingleton_apply_self a by rwa [← hc]⟩

Depends on / 依赖: Submodule, Submodule.injective_subtype, dual_surjective_of_injective, eq_zero_of_ofSpanSingleton_apply_self, injective_subtype, ne_zero, ofSpanSingleton
-/
lemma exists_character_apply_ne_zero_of_ne_zero {a : A} (ne_zero : a != 0) :
    exists (c : CharacterModule A), c a != 0 :=
  have ⟨c, hc⟩ := dual_surjective_of_injective _ (Submodule.injective_subtype _) (ofSpanSingleton a)
⟨c, fun h => ne_zero eq_zero_of_ofSpanSingleton_apply_self a by rwa [← hc]⟩

/--
lemma `eq_zero_of_character_apply` / 引理 `eq_zero_of_character_apply`

English:
lemma eq_zero_of_character_apply
  given: {a : A} (h : forall c : CharacterModule A, c a = 0)
  statement: a = 0
  proof: by
  contrapose! h; exact exists_character_apply_ne_zero_of_ne_zero h

中文:
引理 eq_zero_of_character_apply
  条件: {a : A} (h : 对任意 c : CharacterModule A, c a = 0)
  结论: a = 0
  证明: by
  contrapose! h; exact exists_character_apply_ne_zero_of_ne_zero h

Depends on / 依赖: contrapose, exists_character_apply_ne_zero_of_ne_zero
-/
lemma eq_zero_of_character_apply {a : A} (h : forall c : CharacterModule A, c a = 0) : a = 0 := by
  contrapose! h; exact exists_character_apply_ne_zero_of_ne_zero h

variable [Module R A] [Module R A'] [Module R B] {R A' B}

/--
lemma `dual_surjective_iff_injective` / 引理 `dual_surjective_iff_injective`

English:
lemma dual_surjective_iff_injective
  given: {f : A ->ₗ[R] A'}
  proof: ⟨fun h => (injective_iff_map_eq_zero _).2 fun a h0 => eq_zero_of_character_apply fun c => by
    obtain ⟨c, rfl⟩ := h c; exact congr(c $h0).trans c.map_zero,
  dual_surjective_of_injective f⟩

中文:
引理 dual_surjective_iff_injective
  条件: {f : A ->ₗ[R] A'}
  证明: ⟨fun h => (injective_iff_map_eq_zero _).2 fun a h0 => eq_zero_of_character_apply fun c => by
    obtain ⟨c, rfl⟩ := h c; exact congr(c $h0).trans c.map_zero,
  dual_surjective_of_injective f⟩

Depends on / 依赖: c.map_zero, dual_surjective_of_injective, eq_zero_of_character_apply, injective_iff_map_eq_zero, map_zero
-/
lemma dual_surjective_iff_injective {f : A ->ₗ[R] A'} :
    Function.Surjective (dual f) ↔ Function.Injective f :=
  ⟨fun h => (injective_iff_map_eq_zero _).2 fun a h0 => eq_zero_of_character_apply fun c => by
    obtain ⟨c, rfl⟩ := h c; exact congr(c $h0).trans c.map_zero,
  dual_surjective_of_injective f⟩

/--
theorem `_root_.rTensor_injective_iff_lcomp_surjective` / 定理 `_root_.rTensor_injective_iff_lcomp_surjective`

English:
theorem _root_.rTensor_injective_iff_lcomp_surjective
  given: {f : A ->ₗ[R] A'}
  proof: by
  simp [← dual_rTensor_conj_homEquiv, dual_surjective_iff_injective]

中文:
定理 _root_.rTensor_injective_iff_lcomp_surjective
  条件: {f : A ->ₗ[R] A'}
  证明: by
  simp [← dual_rTensor_conj_homEquiv, dual_surjective_iff_injective]

Depends on / 依赖: dual_rTensor_conj_homEquiv, dual_surjective_iff_injective
-/
theorem _root_.rTensor_injective_iff_lcomp_surjective {f : A ->ₗ[R] A'} :
    Function.Injective (f.rTensor B) ↔ Function.Surjective (f.lcomp R <| CharacterModule B) := by
  simp [← dual_rTensor_conj_homEquiv, dual_surjective_iff_injective]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `surjective_of_dual_injective` / 引理 `surjective_of_dual_injective`

English:
lemma surjective_of_dual_injective
  given: (f : A ->ₗ[R] A') (hf : Function.Injective (dual f))
  proof: by
  rw [← LinearMap.range_eq_top]; rw [← Submodule.unique_quotient_iff_eq_top]
  refine ⟨Unique.mk inferInstance fun a => eq_zero_of_character_apply fun c => ?_⟩
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  suffices eq : dual (Submodule.mkQ _) c = 0 from congr($eq b)
  refine hf ?_
  

中文:
引理 surjective_of_dual_injective
  条件: (f : A ->ₗ[R] A') (hf : 函数.单射 (dual f))
  证明: by
  rw [← LinearMap.range_eq_top]; rw [← Submodule.unique_quotient_iff_eq_top]
  refine ⟨Unique.mk inferInstance fun a => eq_zero_of_character_apply fun c => ?_⟩
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  suffices eq : dual (Submodule.mkQ _) c = 0 from congr($eq b)
  refine hf ?_
  

Depends on / 依赖: AddMonoidHom, AddMonoidHom.zero_comp, LinearMap, LinearMap.comp_apply, LinearMap.range_eq_top, LinearMap.range_mkQ_comp, LinearMap.zero_apply, QuotientAddGroup, QuotientAddGroup.mk, Submodule, Submodule.mkQ, Submodule.unique_quotient_iff_eq_top, Unique, Unique.mk, _surjective, comp_apply, dual_apply, dual_comp, dual_zero, eq_zero_of_character_apply
-/
lemma surjective_of_dual_injective (f : A ->ₗ[R] A') (hf : Function.Injective (dual f)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top]; rw [← Submodule.unique_quotient_iff_eq_top]
  refine ⟨Unique.mk inferInstance fun a => eq_zero_of_character_apply fun c => ?_⟩
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  suffices eq : dual (Submodule.mkQ _) c = 0 from congr($eq b)
  refine hf ?_
  rw [← LinearMap.comp_apply]; rw [← dual_comp]; rw [LinearMap.range_mkQ_comp]; rw [dual_zero]; rw [LinearMap.zero_apply]; rw [dual_apply]; rw [AddMonoidHom.zero_comp]

/--
lemma `dual_injective_iff_surjective` / 引理 `dual_injective_iff_surjective`

English:
lemma dual_injective_iff_surjective
  given: {f : A ->ₗ[R] A'}
  proof: ⟨fun h => surjective_of_dual_injective f h, fun h => dual_injective_of_surjective f h⟩

中文:
引理 dual_injective_iff_surjective
  条件: {f : A ->ₗ[R] A'}
  证明: ⟨fun h => surjective_of_dual_injective f h, fun h => dual_injective_of_surjective f h⟩

Depends on / 依赖: dual_injective_of_surjective, surjective_of_dual_injective
-/
lemma dual_injective_iff_surjective {f : A ->ₗ[R] A'} :
    Function.Injective (dual f) ↔ Function.Surjective f :=
  ⟨fun h => surjective_of_dual_injective f h, fun h => dual_injective_of_surjective f h⟩

/--
lemma `dual_bijective_iff_bijective` / 引理 `dual_bijective_iff_bijective`

English:
lemma dual_bijective_iff_bijective
  given: {f : A ->ₗ[R] A'}
  proof: ⟨fun h => ⟨dual_surjective_iff_injective.mp h.2, dual_injective_iff_surjective.mp h.1⟩,
  fun h => ⟨dual_injective_iff_surjective.mpr h.2, dual_surjective_iff_injective.mpr h.1⟩⟩

中文:
引理 dual_bijective_iff_bijective
  条件: {f : A ->ₗ[R] A'}
  证明: ⟨fun h => ⟨dual_surjective_iff_injective.mp h.2, dual_injective_iff_surjective.mp h.1⟩,
  fun h => ⟨dual_injective_iff_surjective.mpr h.2, dual_surjective_iff_injective.mpr h.1⟩⟩

Depends on / 依赖: dual_injective_iff_surjective, dual_injective_iff_surjective.mp, dual_injective_iff_surjective.mpr, dual_surjective_iff_injective, dual_surjective_iff_injective.mp, dual_surjective_iff_injective.mpr
-/
lemma dual_bijective_iff_bijective {f : A ->ₗ[R] A'} :
    Function.Bijective (dual f) ↔ Function.Bijective f :=
  ⟨fun h => ⟨dual_surjective_iff_injective.mp h.2, dual_injective_iff_surjective.mp h.1⟩,
  fun h => ⟨dual_injective_iff_surjective.mpr h.2, dual_surjective_iff_injective.mpr h.1⟩⟩

end CharacterModule
