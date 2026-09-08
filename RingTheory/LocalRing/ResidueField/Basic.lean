/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Over

/-!

# Residue Field of local rings

We prove basic properties of the residue field of a local ring.

-/

@[expose] public section

variable {R S T : Type*}

namespace IsLocalRing

section

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]

/-
**IsLocalRing.residue_def** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：residue_def (x) : residue R x = Ideal.Quotient.mk (maximalIdeal R) x
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma residue_def (x) : residue R x = Ideal.Quotient.mk (maximalIdeal R) x := rfl
/-
**IsLocalRing.ker_residue** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：ker_residue : RingHom.ker (residue R) = maximalIdeal R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
-/
lemma ker_residue : RingHom.ker (residue R) = maximalIdeal R :=
  Ideal.mk_ker

@[simp]
/-
**IsLocalRing.residue_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：residue_eq_zero_iff (x : R) : residue R x = 0 ↔ x in maximalIdeal R
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用引理 `IsLocalRing.ker_residue`：ker_residue : RingHom.ker (residue R) = maximal
Ideal R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma residue_eq_zero_iff (x : R) : residue R x = 0 ↔ x ∈ maximalIdeal R := by
  rw [← RingHom.mem_ker, ker_residue]
/-
**IsLocalRing.residue_ne_zero_iff_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`
。
形式化陈述：residue_ne_zero_iff_isUnit (x : R) : residue R x != 0 ↔ IsUnit x
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma residue_ne_zero_iff_isUnit (x : R) : residue R x ≠ 0 ↔ IsUnit x := by
  simp
/-
**IsLocalRing.residue_surjective** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRing`。
形式化陈述：residue_surjective : Function.Surjective (IsLocalRing.residue R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
-/
lemma residue_surjective :
    Function.Surjective (IsLocalRing.residue R) :=
  Ideal.Quotient.mk_surjective

variable (R)
/-
**IsLocalRing.ResidueField.algebra** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing.Residu
eField`。
形式化陈述：(R : Type u_1) →   [inst : CommRing R] →     [inst_1 : IsLocalRing R] →   
    {R₀ : Type u_4} → [inst_2 : CommRing R₀] → [Algebra R₀ R] → Algebra R₀ (IsLo
calRing.ResidueField R)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ResidueField.algebra {R₀} [CommRing R₀] [Algebra R₀ R] :
    Algebra R₀ (ResidueField R) :=
  inferInstanceAs <| Algebra R₀ (_ ⧸ _)
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₁ R₂} [CommRing R₁] [CommRing R₂]
    [Algebra R₁ R₂] [Algebra R₁ R] [Algebra R₂ R] [IsScalarTower R₁ R₂ R] :
    IsScalarTower R₁ R₂ (ResidueField R) :=
  inferInstanceAs <| IsScalarTower R₁ R₂ (_ ⧸ _)

@[simp]
/-
**IsLocalRing.ResidueField.algebraMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.
ResidueField`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsLocalRing R],   algebraMa
p R (IsLocalRing.ResidueField R) = IsLocalRing.residue R
参数：R : Type u_1；IsLocalRing.ResidueField R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ResidueField.algebraMap_eq : algebraMap R (ResidueField R) = residue R :=
  rfl
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalHom (IsLocalRing.residue R) :=
  ⟨fun _ ha =>
    Classical.not_not.mp (Ideal.Quotient.eq_zero_iff_mem.not.mp (isUnit_iff_ne_zero.mp ha))⟩

#adaptation_note /-- Needed after leanprover/lean4#12564 -/
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Needed after leanprover/lean4#12564
-/
noncomputable instance {R₀} [CommRing R₀] [Algebra R₀ R] : Module R₀ (ResidueField R) :=
  inferInstanceAs <| Module R₀ (R ⧸ maximalIdeal R)
/-
**IsLocalRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀} [CommRing R₀] [Algebra R₀ R] [Module.Finite R₀ R] :
    Module.Finite R₀ (ResidueField R) :=
  .of_surjective (IsScalarTower.toAlgHom R₀ R _).toLinearMap Ideal.Quotient.mk_surjective

variable {R}

namespace ResidueField

/-- A local ring homomorphism into a field can be descended onto the residue field. -/
/-
**IsLocalRing.ResidueField.lift** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing.ResidueFi
eld`。
形式化陈述：lift {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R ->+* S) [
IsLocalHom f] : IsLocalRing.ResidueField R ->+* S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A local ring homomorphism into a field can be descended onto the residue field.
-/
def lift {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R →+* S) [IsLocalHom f] :
    IsLocalRing.ResidueField R →+* S :=
  Ideal.Quotient.lift _ f fun a ha =>
    by_contradiction fun h => ha (isUnit_of_map_unit f a (isUnit_iff_ne_zero.mpr h))
/-
**IsLocalRing.ResidueField.lift_comp_residue** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalR
ing.ResidueField`。
形式化陈述：lift_comp_residue {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f 
: R ->+* S) [IsLocalHom f] : (lift f).comp (residue R) = f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
-/
theorem lift_comp_residue {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R →+* S)
    [IsLocalHom f] : (lift f).comp (residue R) = f :=
  RingHom.ext fun _ => rfl

@[simp]
/-
**IsLocalRing.ResidueField.lift_residue_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
Ring.ResidueField`。
形式化陈述：lift_residue_apply {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f
 : R ->+* S) [IsLocalHom f] (x) : lift f (residue R x) = f x
参数：f : R ->+* S；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_residue_apply {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R →+* S)
    [IsLocalHom f] (x) : lift f (residue R x) = f x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The map on residue fields induced by a local homomorphism between local rings -/
/-
**IsLocalRing.ResidueField.map** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing.ResidueFie
ld`。
形式化陈述：map (f : R ->+* S) [IsLocalHom f] : ResidueField R ->+* ResidueField S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map on residue fields induced by a local homomorphism between local rings
-/
noncomputable def map (f : R →+* S) [IsLocalHom f] : ResidueField R →+* ResidueField S :=
  Ideal.Quotient.lift (maximalIdeal R) ((Ideal.Quotient.mk _).comp f) fun a ha => by
    unfold ResidueField
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact map_nonunit f a ha

/-- Applying `IsLocalRing.ResidueField.map` to the identity ring homomorphism gives the identity
ring homomorphism. -/
@[simp]
/-
**IsLocalRing.ResidueField.map_id** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.Residue
Field`。
形式化陈述：map_id : IsLocalRing.ResidueField.map (RingHom.id R) = RingHom.id (IsLocal
Ring.ResidueField R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `isLocalHom_id`：isLocalHom_id (R : Type*) [Semiring R] : IsLocalHom (Ring
Hom.id R) where map_nonunit _
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g

--- 原说明 ---
Applying `IsLocalRing.ResidueField.map` to the identity ring homomorphism gives 
the identity
ring homomorphism.
-/
theorem map_id :
    IsLocalRing.ResidueField.map (RingHom.id R) = RingHom.id (IsLocalRing.ResidueField R) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun _ => rfl

/-- The composite of two `IsLocalRing.ResidueField.map`s is the `IsLocalRing.ResidueField.map` of
the composite. -/
/-
**IsLocalRing.ResidueField.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.Resid
ueField`。
形式化陈述：map_comp (f : T ->+* R) (g : R ->+* S) [IsLocalHom f] [IsLocalHom g] : IsL
ocalRing.ResidueField.map (g.comp f) = (IsLocalRing.ResidueField.map g).comp (Is
LocalRing.ResidueField.map f)
参数：f : T ->+* R；g : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingHom.isLocalHom_comp`：RingHom.isLocalHom_comp (g : S ->+* T) (f : R -
>+* S) [IsLocalHom g] [IsLocalHom f] : IsLocalHom (g.comp f) where map_nonunit a
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g

--- 原说明 ---
The composite of two `IsLocalRing.ResidueField.map`s is the `IsLocalRing.Residue
Field.map` of
the composite.
-/
theorem map_comp (f : T →+* R) (g : R →+* S) [IsLocalHom f] [IsLocalHom g] :
    IsLocalRing.ResidueField.map (g.comp f) =
      (IsLocalRing.ResidueField.map g).comp (IsLocalRing.ResidueField.map f) :=
  Ideal.Quotient.ringHom_ext <| RingHom.ext fun _ => rfl
/-
**IsLocalRing.ResidueField.map_comp_residue** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRi
ng.ResidueField`。
形式化陈述：map_comp_residue (f : R ->+* S) [IsLocalHom f] : (ResidueField.map f).comp
 (residue R) = (residue S).comp f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_residue (f : R →+* S) [IsLocalHom f] :
    (ResidueField.map f).comp (residue R) = (residue S).comp f :=
  rfl

@[simp]
/-
**IsLocalRing.ResidueField.map_residue** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.Re
sidueField`。
形式化陈述：map_residue (f : R ->+* S) [IsLocalHom f] (r : R) : ResidueField.map f (re
sidue R r) = residue S (f r)
参数：f : R ->+* S；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_residue (f : R →+* S) [IsLocalHom f] (r : R) :
    ResidueField.map f (residue R r) = residue S (f r) :=
  rfl
/-
**IsLocalRing.ResidueField.map_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.R
esidueField`。
形式化陈述：map_id_apply (x : ResidueField R) : map (RingHom.id R) x = x
参数：x : ResidueField R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `isLocalHom_id`：isLocalHom_id (R : Type*) [Semiring R] : IsLocalHom (Ring
Hom.id R) where map_nonunit _
· 使用定理 `IsLocalRing.ResidueField.map_id`：map_id : IsLocalRing.ResidueField.map (
RingHom.id R) = RingHom.id (IsLocalRing.ResidueField R)
-/
theorem map_id_apply (x : ResidueField R) : map (RingHom.id R) x = x :=
  DFunLike.congr_fun map_id x

@[simp]
/-
**IsLocalRing.ResidueField.map_map** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.Residu
eField`。
形式化陈述：map_map (f : R ->+* S) (g : S ->+* T) (x : ResidueField R) [IsLocalHom f] 
[IsLocalHom g] : map g (map f x) = map (g.comp f) x
参数：f : R ->+* S；g : S ->+* T；x : ResidueField R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `RingHom.isLocalHom_comp`：RingHom.isLocalHom_comp (g : S ->+* T) (f : R -
>+* S) [IsLocalHom g] [IsLocalHom f] : IsLocalHom (g.comp f) where map_nonunit a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.ResidueField.map_comp`：map_comp (f : T ->+* R) (g : R ->+* S
) [IsLocalHom f] [IsLocalHom g] : IsLocalRing.ResidueField.map (g.comp f) = (IsL
ocalRing.ResidueField.m…
-/
theorem map_map (f : R →+* S) (g : S →+* T) (x : ResidueField R) [IsLocalHom f]
    [IsLocalHom g] : map g (map f x) = map (g.comp f) x :=
  DFunLike.congr_fun (map_comp f g).symm x

/-- A ring isomorphism defines an isomorphism of residue fields. -/
@[simps apply]
/-
**IsLocalRing.ResidueField.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing.Resid
ueField`。
形式化陈述：mapEquiv (f : R ≃+* S) : IsLocalRing.ResidueField R ≃+* IsLocalRing.Residu
eField S where toFun
参数：f : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring isomorphism defines an isomorphism of residue fields.
-/
noncomputable def mapEquiv (f : R ≃+* S) :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S where
  toFun := map (f : R →+* S)
  invFun := map (f.symm : S →+* R)
  left_inv x := by simp only [map_map, RingEquiv.symm_comp, map_id, RingHom.id_apply]
  right_inv x := by simp only [map_map, RingEquiv.comp_symm, map_id, RingHom.id_apply]
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
/-
**IsLocalRing.ResidueField.mapEquiv.symm** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.
ResidueField.mapEquiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : IsLocalRing 
R] [inst_2 : CommRing S]   [inst_3 : IsLocalRing S] (f : R ≃+* S),   (IsLocalRin
g.ResidueField.mapEquiv f).symm = IsLocalRing.ResidueField.mapEquiv f.symm
参数：f : R ≃+* S；IsLocalRing.ResidueField.mapEquiv f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapEquiv.symm (f : R ≃+* S) : (mapEquiv f).symm = mapEquiv f.symm :=
  rfl

@[simp]
/-
**IsLocalRing.ResidueField.mapEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing
.ResidueField`。
形式化陈述：mapEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) : mapEquiv (e₁.trans e₂) = (m
apEquiv e₁).trans (mapEquiv e₂)
参数：e₁ : R ≃+* S；e₂ : S ≃+* T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.toRingHom_injective`：toRingHom_injective : Function.Injective 
(toRingHom : R ≃+* S -> R ->+* S)
· 使用定理 `IsLocalRing.ResidueField.map_comp`：map_comp (f : T ->+* R) (g : R ->+* S
) [IsLocalHom f] [IsLocalHom g] : IsLocalRing.ResidueField.map (g.comp f) = (IsL
ocalRing.ResidueField.m…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `isLocalHom_toRingHom`：isLocalHom_toRingHom {F : Type*} [FunLike F R S] [
RingHomClass F R S] (f : F) [IsLocalHom f] : IsLocalHom (f : R ->+* S)
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
-/
theorem mapEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    mapEquiv (e₁.trans e₂) = (mapEquiv e₁).trans (mapEquiv e₂) :=
  RingEquiv.toRingHom_injective <| map_comp (e₁ : R →+* S) (e₂ : S →+* T)

@[simp]
/-
**IsLocalRing.ResidueField.mapEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.
ResidueField`。
形式化陈述：mapEquiv_refl : mapEquiv (RingEquiv.refl R) = RingEquiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.toRingHom_injective`：toRingHom_injective : Function.Injective 
(toRingHom : R ≃+* S -> R ->+* S)
· 使用定理 `IsLocalRing.ResidueField.map_id`：map_id : IsLocalRing.ResidueField.map (
RingHom.id R) = RingHom.id (IsLocalRing.ResidueField R)
-/
theorem mapEquiv_refl : mapEquiv (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.toRingHom_injective map_id

/-- The group homomorphism from `RingAut R` to `RingAut k` where `k`
is the residue field of `R`. -/
@[simps]
/-
**IsLocalRing.ResidueField.mapAut** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing.Residue
Field`。
形式化陈述：mapAut : RingAut R ->* RingAut (IsLocalRing.ResidueField R) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.ResidueField.mapEquiv_refl`：mapEquiv_refl : mapEquiv (RingEq
uiv.refl R) = RingEquiv.refl _
· 使用定理 `IsLocalRing.ResidueField.mapEquiv_trans`：mapEquiv_trans (e₁ : R ≃+* S) (
e₂ : S ≃+* T) : mapEquiv (e₁.trans e₂) = (mapEquiv e₁).trans (mapEquiv e₂)

--- 原说明 ---
The group homomorphism from `RingAut R` to `RingAut k` where `k`
is the residue field of `R`.
-/
noncomputable def mapAut : RingAut R →* RingAut (IsLocalRing.ResidueField R) where
  toFun := mapEquiv
  map_mul' e₁ e₂ := mapEquiv_trans e₂ e₁
  map_one' := mapEquiv_refl

section MulSemiringAction

variable (G : Type*) [Group G] [MulSemiringAction G R]

/-- If `G` acts on `R` as a `MulSemiringAction`, then it also acts on `IsLocalRing.ResidueField R`.
-/
/-
**IsLocalRing.ResidueField.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing.ResidueField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` acts on `R` as a `MulSemiringAction`, then it also acts on `IsLocalRing.R
esidueField R`.
-/
noncomputable instance : MulSemiringAction G (IsLocalRing.ResidueField R) :=
  MulSemiringAction.compHom _ <| mapAut.comp (MulSemiringAction.toRingAut G R)

@[simp]
/-
**IsLocalRing.ResidueField.residue_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing.R
esidueField`。
形式化陈述：residue_smul (g : G) (r : R) : residue R (g • r) = g • residue R r
参数：g : G；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem residue_smul (g : G) (r : R) : residue R (g • r) = g • residue R r :=
  rfl

end MulSemiringAction

section FiniteDimensional

variable [Algebra R S] [IsLocalHom (algebraMap R S)]

/-
**IsLocalRing.ResidueField.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing.ResidueField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (maximalIdeal S).LiesOver (maximalIdeal R) :=
  ⟨(((local_hom_TFAE (algebraMap R S)).out 0 4 rfl rfl).mp inferInstance).symm⟩
/-
**IsLocalRing.ResidueField.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing.ResidueField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra (ResidueField R) (ResidueField S) :=
  Ideal.Quotient.algebraOfLiesOver _ _
/-
**IsLocalRing.ResidueField.algebraMap_residue** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
Ring.ResidueField`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : IsLocalRing 
R] [inst_2 : CommRing S]   [inst_3 : IsLocalRing S] [inst_4 : Algebra R S] [inst
_5 : IsLocalHom (algebraMap R S)] (x : R),   (algebraMap (IsLocalRing.ResidueFie
ld R) (IsLocalRing.ResidueField S)) ((IsLocalRing.residue R) x) =     (IsLocalRi
ng.residue S) ((algebraMap R S) x)
参数：algebraMap R S；x : R；algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.Res
idueField S)；(IsLocalRing.residue R) x；IsLocalRing.residue S；(algebraMap R S) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma algebraMap_residue (x : R) :
    algebraMap (ResidueField R) (ResidueField S) (residue R x) =
      residue S (algebraMap R S x) := rfl
/-
**IsLocalRing.ResidueField.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing.ResidueField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    IsScalarTower R₀ (ResidueField R) (ResidueField S) :=
  Ideal.Quotient.isScalarTower_of_liesOver ..
/-
**IsLocalRing.ResidueField.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing.ResidueField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
    [IsLocalRing R₀] [IsLocalHom (algebraMap R₀ R)] [IsLocalHom (algebraMap R₀ S)] :
    IsScalarTower (ResidueField R₀) (ResidueField R) (ResidueField S) := by
  refine .of_algebraMap_eq fun x ↦ ?_
  obtain ⟨x, rfl⟩ := residue_surjective x
  simp [← IsScalarTower.algebraMap_apply]

#adaptation_note /-- Needed after leanprover/lean4#12564 -/
/-
**IsLocalRing.ResidueField.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalRing.ResidueField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Needed after leanprover/lean4#12564
-/
noncomputable instance : Module (ResidueField R) (ResidueField S) :=
  inferInstanceAs <| Module (R ⧸ maximalIdeal R) (S ⧸ maximalIdeal S)
/-
**IsLocalRing.ResidueField.finite_of_module_finite** 是 Mathlib 中的一个实例，位于命名空间 `Is
LocalRing.ResidueField`。
形式化陈述：finite_of_module_finite [Module.Finite R S] : Module.Finite (ResidueField 
R) (ResidueField S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst_3
 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `IsLocalRing.instFiniteResidueField`：∀ (R : Type u_1) [inst : CommRing R]
 [inst_1 : IsLocalRing R] {R₀ : Type u_4} [inst_2 : CommRing R₀]   [inst_3 : Alg
ebra R₀ R] [Module.Finit…
-/
instance finite_of_module_finite [Module.Finite R S] :
    Module.Finite (ResidueField R) (ResidueField S) :=
  .of_restrictScalars_finite R _ _
/-
**IsLocalRing.ResidueField.finite_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalRi
ng.ResidueField`。
形式化陈述：finite_of_finite [Module.Finite R S] (hfin : Finite (ResidueField R)) : Fi
nite (ResidueField S)
参数：hfin : Finite (ResidueField R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_finite`：∀ (R : Type u_1) {M : Type u_2} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite R]   [Modul
e.Finite R M]…
-/
lemma finite_of_finite [Module.Finite R S] (hfin : Finite (ResidueField R)) :
    Finite (ResidueField S) := Module.finite_of_finite (ResidueField R)

end FiniteDimensional

omit [IsLocalRing R]

variable [Algebra R S] [Algebra R T]

/-- A local algebra homomorphism induces an algebra homomorphism on the residue fields.

See `mapAlgHom'` for a variant where the base ring `R` is also quotiented. -/
/-
**IsLocalRing.ResidueField.mapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing.Resi
dueField`。
形式化陈述：mapAlgHom (e : S ->ₐ[R] T) [IsLocalHom e] : ResidueField S ->ₐ[R] ResidueF
ield T where __
参数：e : S ->ₐ[R] T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A local algebra homomorphism induces an algebra homomorphism on the residue fiel
ds.

See `mapAlgHom'` for a variant where the base ring `R` is also quotiented.
-/
noncomputable def mapAlgHom (e : S →ₐ[R] T) [IsLocalHom e] :
    ResidueField S →ₐ[R] ResidueField T where
  __ := map e
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply R S (ResidueField S),
      IsScalarTower.algebraMap_apply R T (ResidueField T)]

@[simp]
/-
**IsLocalRing.ResidueField.mapAlgHom_residue** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalR
ing.ResidueField`。
形式化陈述：mapAlgHom_residue (e : S ->ₐ[R] T) [IsLocalHom e] (x : S) : mapAlgHom e (r
esidue S x) = residue T (e x)
参数：e : S ->ₐ[R] T；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAlgHom_residue (e : S →ₐ[R] T) [IsLocalHom e] (x : S) :
    mapAlgHom e (residue S x) = residue T (e x) :=
  rfl

/-- A local algebra isomorphism induces an algebra isomorphism on the residue fields.

See `mapAlgEquiv'` for a variant where the base ring `R` is also quotiented. -/
/-
**IsLocalRing.ResidueField.mapAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing.Re
sidueField`。
形式化陈述：mapAlgEquiv (e : S ≃ₐ[R] T) : ResidueField S ≃ₐ[R] ResidueField T where __
参数：e : S ≃ₐ[R] T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A local algebra isomorphism induces an algebra isomorphism on the residue fields
.

See `mapAlgEquiv'` for a variant where the base ring `R` is also quotiented.
-/
noncomputable def mapAlgEquiv (e : S ≃ₐ[R] T) : ResidueField S ≃ₐ[R] ResidueField T where
  __ := mapAlgHom e.toAlgHom
  __ := mapEquiv e.toRingEquiv

@[simp]
/-
**IsLocalRing.ResidueField.mapAlgEquiv_residue** 是 Mathlib 中的一个定理，位于命名空间 `IsLoca
lRing.ResidueField`。
形式化陈述：mapAlgEquiv_residue (e : S ≃ₐ[R] T) (x : S) : mapAlgEquiv e (residue S x) 
= residue T (e x)
参数：e : S ≃ₐ[R] T；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAlgEquiv_residue (e : S ≃ₐ[R] T) (x : S) :
    mapAlgEquiv e (residue S x) = residue T (e x) :=
  rfl

variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]

/-- A local algebra homomorphism induces an algebra homomorphism on the residue fields.

See `mapAlgHom` for a variant where the base ring `R` is not quotiented. -/
/-
**IsLocalRing.ResidueField.mapAlgHom'** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing.Res
idueField`。
形式化陈述：mapAlgHom' (e : S ->ₐ[R] T) [IsLocalHom e] : ResidueField S ->ₐ[ResidueFie
ld R] ResidueField T
参数：e : S ->ₐ[R] T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalRing.residue_surjective`：residue_surjective : Function.Surjective
 (IsLocalRing.residue R)

--- 原说明 ---
A local algebra homomorphism induces an algebra homomorphism on the residue fiel
ds.

See `mapAlgHom` for a variant where the base ring `R` is not quotiented.
-/
noncomputable def mapAlgHom' (e : S →ₐ[R] T) [IsLocalHom e] :
    ResidueField S →ₐ[ResidueField R] ResidueField T :=
  (mapAlgHom e).extendScalarsOfSurjective residue_surjective

@[simp]
/-
**IsLocalRing.ResidueField.mapAlgHom'_residue** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
Ring.ResidueField`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : IsLocalRing S]   [inst_3 : CommRing T] [inst_4 : IsLoca
lRing T] [inst_5 : Algebra R S] [inst_6 : Algebra R T]   [inst_7 : IsLocalHom (a
lgebraMap R S)] [inst_8 : IsLocalHom (algebraMap R T)] [inst_9 : IsLocalRing R] 
(e : S →ₐ[R] T)   [inst_10 : IsLocalHom e] (x : S),   (IsLocalRing.ResidueField.
mapAlgHom' e) ((IsLocalRing.residue S) x) = (IsLocalRing.residue T) (e x)
参数：algebraMap R S；algebraMap R T；e : S →ₐ[R] T；x : S；IsLocalRing.ResidueField.ma
pAlgHom' e；(IsLocalRing.residue S) x；IsLocalRing.residue T；e x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAlgHom'_residue [IsLocalRing R] (e : S →ₐ[R] T) [IsLocalHom e] (x : S) :
    mapAlgHom' e (residue S x) = residue T (e x) :=
  rfl

/-- A local algebra isomorphism induces an algebra isomorphism on the residue fields.

See `mapAlgEquiv` for a variant where the base ring `R` is not quotiented. -/
/-
**IsLocalRing.ResidueField.mapAlgEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing.R
esidueField`。
形式化陈述：mapAlgEquiv' (e : S ≃ₐ[R] T) : ResidueField S ≃ₐ[ResidueField R] ResidueFi
eld T
参数：e : S ≃ₐ[R] T。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalRing.residue_surjective`：residue_surjective : Function.Surjective
 (IsLocalRing.residue R)

--- 原说明 ---
A local algebra isomorphism induces an algebra isomorphism on the residue fields
.

See `mapAlgEquiv` for a variant where the base ring `R` is not quotiented.
-/
noncomputable def mapAlgEquiv' (e : S ≃ₐ[R] T) :
    ResidueField S ≃ₐ[ResidueField R] ResidueField T :=
  (mapAlgEquiv e).extendScalarsOfSurjective residue_surjective

@[simp]
/-
**IsLocalRing.ResidueField.mapAlgEquiv'_residue** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alRing.ResidueField`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : IsLocalRing S]   [inst_3 : CommRing T] [inst_4 : IsLoca
lRing T] [inst_5 : Algebra R S] [inst_6 : Algebra R T]   [inst_7 : IsLocalHom (a
lgebraMap R S)] [inst_8 : IsLocalHom (algebraMap R T)] [inst_9 : IsLocalRing R] 
(e : S ≃ₐ[R] T)   (x : S), (IsLocalRing.ResidueField.mapAlgEquiv' e) ((IsLocalRi
ng.residue S) x) = (IsLocalRing.residue T) (e x)
参数：algebraMap R S；algebraMap R T；e : S ≃ₐ[R] T；x : S；IsLocalRing.ResidueField.ma
pAlgEquiv' e；(IsLocalRing.residue S) x；IsLocalRing.residue T；e x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAlgEquiv'_residue [IsLocalRing R] (e : S ≃ₐ[R] T) (x : S) :
    mapAlgEquiv' e (residue S x) = residue T (e x) :=
  rfl

end ResidueField

end

end IsLocalRing

