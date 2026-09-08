/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes, Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The abelianization of a group

This file defines the commutator and the abelianization of a group. It furthermore prepares for the
result that the abelianization is left adjoint to the forgetful functor from abelian groups to
groups, which can be found in `Mathlib/Algebra/Category/Grp/Adjunctions.lean`.

## Main definitions

* `Abelianization`: defines the abelianization of a group `G` as the quotient of a group by its
  commutator subgroup.
* `Abelianization.map`: lifts a group homomorphism to a homomorphism between the abelianizations
* `MulEquiv.abelianizationCongr`: Equivalent groups have equivalent abelianizations

-/

@[expose] public section

assert_not_exists Cardinal Field

universe u v w

-- Let G be a group.
variable (G : Type u) [Group G]

open Subgroup (centralizer)

/-- The abelianization of G is the quotient of G by its commutator subgroup. -/
/-
**Abelianization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Abelianization : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The abelianization of G is the quotient of G by its commutator subgroup.
-/
def Abelianization : Type u :=
  G ⧸ commutator G

namespace Abelianization

/-
**Abelianization.commGroup** 是 Mathlib 中的一个实例，位于命名空间 `Abelianization`。
形式化陈述：commGroup : CommGroup (Abelianization G) where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instNormalCommutator`：∀ (G : Type u_1) [inst : Group G], (commutator G).
Normal
-/
instance commGroup : CommGroup (Abelianization G) where
  __ := QuotientGroup.Quotient.group _
  mul_comm x y := Quotient.inductionOn₂ x y fun a b ↦ Quotient.sound' <|
    QuotientGroup.leftRel_apply.mpr <| Subgroup.subset_closure
      -- We avoid `group` here to minimize imports while low in the hierarchy;
      -- typically it would be better to invoke the tactic.
      ⟨b⁻¹, Subgroup.mem_top _, a⁻¹, Subgroup.mem_top _, by simp [commutatorElement_def, mul_assoc]⟩
/-
**Abelianization.** 是 Mathlib 中的一个实例，位于命名空间 `Abelianization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Abelianization G) :=
  ⟨1⟩

variable {G}

/-- `of` is the canonical projection from G to its abelianization. -/
/-
**Abelianization.of** 是 Mathlib 中的一个定义，位于命名空间 `Abelianization`。
形式化陈述：of : G ->* Abelianization G where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`of` is the canonical projection from G to its abelianization.
-/
def of : G →* Abelianization G where
  toFun := QuotientGroup.mk
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/-
**Abelianization.mk_eq_of** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：mk_eq_of (a : G) : Quot.mk _ a = of a
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_eq_of (a : G) : Quot.mk _ a = of a :=
  rfl

variable (G) in
@[simp]
/-
**Abelianization.ker_of** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：ker_of : of.ker = commutator G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `instNormalCommutator`：∀ (G : Type u_1) [inst : Group G], (commutator G).
Normal
-/
theorem ker_of : of.ker = commutator G :=
  QuotientGroup.ker_mk' (commutator G)

section lift

-- So far we have built Gᵃᵇ and proved it's an abelian group.
-- Furthermore we defined the canonical projection `of : G → Gᵃᵇ`
-- Let `A` be an abelian group and let `f` be a group homomorphism from `G` to `A`.
variable {A : Type v} [CommGroup A] (f : G →* A)

/-
**Abelianization.commutator_subset_ker** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization
`。
形式化陈述：commutator_subset_ker : commutator G <= f.ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `commutator_eq_closure`：commutator_eq_closure : commutator G = Subgroup.c
losure (commutatorSet G)
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem commutator_subset_ker : commutator G ≤ f.ker := by
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro x ⟨p, q, rfl⟩
  simp [MonoidHom.mem_ker, mul_right_comm (f p) (f q), commutatorElement_def]

/-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map
  from the abelianization of a `G` to `A` that factors through `f`. -/
/-
**Abelianization.lift** 是 Mathlib 中的一个定义，位于命名空间 `Abelianization`。
形式化陈述：lift : (G ->* A) ≃ (Abelianization G ->* A) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNormalCommutator`：∀ (G : Type u_1) [inst : Group G], (commutator G).
Normal

--- 原说明 ---
If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the
 unique map
  from the abelianization of a `G` to `A` that factors through `f`.
-/
def lift : (G →* A) ≃ (Abelianization G →* A) where
  toFun f := QuotientGroup.lift _ f fun _ h => MonoidHom.mem_ker.2 <| commutator_subset_ker _ h
  invFun F := F.comp of
  right_inv _ := MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

@[simp]
/-
**Abelianization.lift_apply_of** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：lift_apply_of (x : G) : lift f (of x) = f x
参数：x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_apply_of (x : G) : lift f (of x) = f x :=
  rfl
/-
**Abelianization.coe_lift_symm** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：coe_lift_symm : (lift.symm : (Abelianization G ->* A) -> (G ->* A)) = (·.c
omp of)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_lift_symm : (lift.symm : (Abelianization G →* A) → (G →* A)) = (·.comp of) := rfl

@[simp]
/-
**Abelianization.lift_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：lift_symm_apply (f : Abelianization G ->* A) : lift.symm f = f.comp of
参数：f : Abelianization G ->* A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_symm_apply (f : Abelianization G →* A) : lift.symm f = f.comp of := rfl
/-
**Abelianization.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：lift_unique (φ : Abelianization G ->* A) -- hφ : φ agrees with f on the im
age of G in Gᵃᵇ (hφ : forall x : G, φ (Abelianization.of x) = f x) {x : Abeliani
zation G} : φ x = lift f x
参数：φ : Abelianization G ->* A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
-/
theorem lift_unique (φ : Abelianization G →* A)
    -- hφ : φ agrees with f on the image of G in Gᵃᵇ
    (hφ : ∀ x : G, φ (Abelianization.of x) = f x)
    {x : Abelianization G} : φ x = lift f x :=
  QuotientGroup.induction_on x hφ

@[simp]
/-
**Abelianization.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：lift_of : lift of = MonoidHom.id (Abelianization G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem lift_of : lift of = MonoidHom.id (Abelianization G) :=
  lift.apply_symm_apply <| MonoidHom.id _

end lift

variable {A : Type v} [Monoid A]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
/-
**Abelianization.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：hom_ext (φ ψ : Abelianization G ->* A) (h : φ.comp of = ψ.comp of) : φ = ψ
参数：φ ψ : Abelianization G ->* A；h : φ.comp of = ψ.comp of。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem hom_ext (φ ψ : Abelianization G →* A) (h : φ.comp of = ψ.comp of) : φ = ψ :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x <| DFunLike.congr_fun h

section Map

variable {H : Type v} [Group H] (f : G →* H)

/-- The map operation of the `Abelianization` functor -/
/-
**Abelianization.map** 是 Mathlib 中的一个定义，位于命名空间 `Abelianization`。
形式化陈述：map : Abelianization G ->* Abelianization H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map operation of the `Abelianization` functor
-/
def map : Abelianization G →* Abelianization H :=
  lift (of.comp f)

/-- Use `map` as the preferred simp normal form. -/
/-
**Abelianization.lift_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：∀ {G : Type u} [inst : Group G] {H : Type v} [inst_1 : Group H] (f : G →* 
H),   Abelianization.lift (Abelianization.of.comp f) = Abelianization.map f
参数：f : G →* H；Abelianization.of.comp f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `map` as the preferred simp normal form.
-/
@[simp] theorem lift_of_comp :
    Abelianization.lift (Abelianization.of.comp f) = Abelianization.map f := rfl

@[simp]
/-
**Abelianization.map_of** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：map_of (x : G) : map f (of x) = of (f x)
参数：x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_of (x : G) : map f (of x) = of (f x) :=
  rfl

@[simp]
/-
**Abelianization.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：map_id : map (MonoidHom.id G) = MonoidHom.id (Abelianization G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Abelianization.hom_ext`：hom_ext (φ ψ : Abelianization G ->* A) (h : φ.co
mp of = ψ.comp of) : φ = ψ
-/
theorem map_id : map (MonoidHom.id G) = MonoidHom.id (Abelianization G) :=
  hom_ext _ _ rfl

@[simp]
/-
**Abelianization.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：map_comp {I : Type w} [Group I] (g : H ->* I) : (map g).comp (map f) = map
 (g.comp f)
参数：g : H ->* I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Abelianization.hom_ext`：hom_ext (φ ψ : Abelianization G ->* A) (h : φ.co
mp of = ψ.comp of) : φ = ψ
-/
theorem map_comp {I : Type w} [Group I] (g : H →* I) : (map g).comp (map f) = map (g.comp f) :=
  hom_ext _ _ rfl

@[simp]
/-
**Abelianization.map_map_apply** 是 Mathlib 中的一个定理，位于命名空间 `Abelianization`。
形式化陈述：map_map_apply {I : Type w} [Group I] {g : H ->* I} {x : Abelianization G} 
: map g (map f x) = map (g.comp f) x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Abelianization.map_comp`：map_comp {I : Type w} [Group I] (g : H ->* I) :
 (map g).comp (map f) = map (g.comp f)
-/
theorem map_map_apply {I : Type w} [Group I] {g : H →* I} {x : Abelianization G} :
    map g (map f x) = map (g.comp f) x :=
  DFunLike.congr_fun (map_comp _ _) x

end Map

end Abelianization

section AbelianizationCongr

variable {G} {H : Type v} [Group H]

/-- Equivalent groups have equivalent abelianizations -/
/-
**MulEquiv.abelianizationCongr** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.abelianizationCongr (e : G ≃* H) : Abelianization G ≃* Abelianiza
tion H where toFun
参数：e : G ≃* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalent groups have equivalent abelianizations
-/
def MulEquiv.abelianizationCongr (e : G ≃* H) : Abelianization G ≃* Abelianization H where
  toFun := Abelianization.map e.toMonoidHom
  invFun := Abelianization.map e.symm.toMonoidHom
  left_inv := by
    rintro ⟨a⟩
    simp
  right_inv := by
    rintro ⟨a⟩
    simp
  map_mul' := map_mul _

@[simp]
/-
**abelianizationCongr_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abelianizationCongr_of (e : G ≃* H) (x : G) : e.abelianizationCongr (Abeli
anization.of x) = Abelianization.of (e x)
参数：e : G ≃* H；x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abelianizationCongr_of (e : G ≃* H) (x : G) :
    e.abelianizationCongr (Abelianization.of x) = Abelianization.of (e x) :=
  rfl

@[simp]
/-
**abelianizationCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abelianizationCongr_refl : (MulEquiv.refl G).abelianizationCongr = MulEqui
v.refl (Abelianization G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.toMonoidHom_injective`：toMonoidHom_injective : Injective (toMon
oidHom : M ≃* N -> M ->* N)
· 使用定理 `Abelianization.lift_of`：lift_of : lift of = MonoidHom.id (Abelianization
 G)
-/
theorem abelianizationCongr_refl :
    (MulEquiv.refl G).abelianizationCongr = MulEquiv.refl (Abelianization G) :=
  MulEquiv.toMonoidHom_injective Abelianization.lift_of

@[simp]
/-
**abelianizationCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abelianizationCongr_symm (e : G ≃* H) : e.abelianizationCongr.symm = e.sym
m.abelianizationCongr
参数：e : G ≃* H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abelianizationCongr_symm (e : G ≃* H) :
    e.abelianizationCongr.symm = e.symm.abelianizationCongr :=
  rfl

@[simp]
/-
**abelianizationCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abelianizationCongr_trans {I : Type v} [Group I] (e : G ≃* H) (e₂ : H ≃* I
) : e.abelianizationCongr.trans e₂.abelianizationCongr = (e.trans e₂).abelianiza
tionCongr
参数：e : G ≃* H；e₂ : H ≃* I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.toMonoidHom_injective`：toMonoidHom_injective : Injective (toMon
oidHom : M ≃* N -> M ->* N)
· 使用定理 `Abelianization.hom_ext`：hom_ext (φ ψ : Abelianization G ->* A) (h : φ.co
mp of = ψ.comp of) : φ = ψ
-/
theorem abelianizationCongr_trans {I : Type v} [Group I] (e : G ≃* H) (e₂ : H ≃* I) :
    e.abelianizationCongr.trans e₂.abelianizationCongr = (e.trans e₂).abelianizationCongr :=
  MulEquiv.toMonoidHom_injective (Abelianization.hom_ext _ _ rfl)

end AbelianizationCongr

/-- An Abelian group is equivalent to its own abelianization. -/
@[simps]
/-
**Abelianization.equivOfComm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Abelianization.equivOfComm {H : Type*} [CommGroup H] : H ≃* Abelianization
 H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An Abelian group is equivalent to its own abelianization.
-/
def Abelianization.equivOfComm {H : Type*} [CommGroup H] : H ≃* Abelianization H :=
  { Abelianization.of with
    toFun := Abelianization.of
    invFun := Abelianization.lift (MonoidHom.id H)
    right_inv := by
      rintro ⟨a⟩
      rfl }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique G] : Unique (Abelianization G) := Quotient.instUniqueQuotient _
