/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Weakly étale algebras

In this file we define weakly étale algebras. An `R`-algebra `S` is weakly étale if
`S` is `R`-flat and the multiplication map `S ⊗[R] S → S` is flat.

## TODOs

- Show that a weakly étale algebra is formally unramified and in particular that
  a weakly étale algebra of finite presentation is étale (@chrisflav).
-/

public section

universe u u₁ u₂ u₃

open TensorProduct

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- `S` is a weakly-étale `R`-algebra if both `R → S` and `S ⊗[R] S → R` are flat.
This is also called absolutely flat. -/
@[stacks 092B, mk_iff]
/-
**Algebra.WeaklyEtale** 是 Mathlib 中的一个类，位于命名空间 `Algebra`。
形式化陈述：WeaklyEtale (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] where fl
at : Module.Flat R S
参数：R S : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S` is a weakly-étale `R`-algebra if both `R → S` and `S ⊗[R] S → R` are flat.
This is also called absolutely flat.
-/
class WeaklyEtale (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] where
  flat : Module.Flat R S := by infer_instance
  flat_lmul' (R S) : (Algebra.TensorProduct.lmul' R (S := S)).Flat

attribute [instance] WeaklyEtale.flat

namespace WeaklyEtale

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] ULift.algebra' in
/-
**Algebra.WeaklyEtale.ulift_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.WeaklyEtale`。
形式化陈述：ulift_iff : WeaklyEtale (ULift.{u₁} R) (ULift.{u₂} S) ↔ WeaklyEtale R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.weaklyEtale_iff`：∀ (R : Type u_3) (S : Type u_4) [inst : CommRin
g R] [inst_1 : CommRing S] [inst_2 : Algebra R S],   Algebra.WeaklyEtale R S ↔  
   autoParam …
· 使用引理 `Module.Flat.ulift_left_iff`：ulift_left_iff : Flat (ULift.{t} R) M ↔ Flat
 R M
· 使用引理 `Module.Flat.ulift_right_iff`：ulift_right_iff : Flat R (ULift.{t} M) ↔ Fl
at R M
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RingHom.Flat.ulift_iff`：ulift_iff {f : R ->+* S} : (ulift.{u₁, u₂} f).Fl
at ↔ f.Flat
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.TensorProduct.lmul'_ulift`：∀ (R : Type u_4) (S : Type u_5) [inst
 : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   Algebra.T
ensorProduct.lmul' (ULi…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `AlgHom.comp_toRingHom`：comp_toRingHom (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B
) : (φ₁.comp φ₂ : A ->+* C) = (φ₁ : B ->+* C).comp ↑φ₂
· 使用引理 `RingHom.Flat.comp_iff_of_bijective_right`：comp_iff_of_bijective_right {f
 : R ->+* S} {g : T ->+* R} (hg : Function.Bijective g) : (f.comp g).Flat ↔ f.Fl
at
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma ulift_iff : WeaklyEtale (ULift.{u₁} R) (ULift.{u₂} S) ↔ WeaklyEtale R S := by
  rw [weaklyEtale_iff, weaklyEtale_iff, Module.Flat.ulift_left_iff, Module.Flat.ulift_right_iff]
  congr!
  conv_rhs => rw [← RingHom.Flat.ulift_iff.{u₁, u₂}]
  rw [TensorProduct.lmul'_ulift, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  exact RingHom.Flat.comp_iff_of_bijective_right (Equiv.bijective _)

@[stacks 092N "(2)"]
/-
**Algebra.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.WeaklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Etale R S] : WeaklyEtale R S where
  flat_lmul' := by
    algebraize [Algebra.TensorProduct.lmul' R (S := S) |>.toRingHom]
    have : Etale R (S ⊗[R] S) := .comp _ S _
    have : Etale (S ⊗[R] S) S := .of_restrictScalars R _ _
    exact Smooth.flat (S ⊗[R] S) S

@[stacks 092H "(2)"]
/-
**Algebra.WeaklyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.WeaklyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {T : Type*} [CommRing T] [Algebra R T] [WeaklyEtale R S] :
    WeaklyEtale T (T ⊗[R] S) where
  flat_lmul' := by
    let e : T ⊗[R] S ⊗[T] (T ⊗[R] S) ≃ₐ[T] T ⊗[R] (S ⊗[R] S) :=
      (Algebra.TensorProduct.cancelBaseChange _ _ T _ _).trans
        (TensorProduct.assoc ..)
    have : TensorProduct.lmul' T (S := T ⊗[R] S) =
        (TensorProduct.map (.id T T) (TensorProduct.lmul' R)).comp e.toAlgHom := by
      ext <;> simp [e, TensorProduct.one_def]
    rw [this]
    refine .comp (.of_bijective e.bijective) (.tensorProductMap ?_ ?_)
    · exact .of_bijective Function.bijective_id
    · exact WeaklyEtale.flat_lmul' R S

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] TensorProduct.rightAlgebra ULift.algebra' in
@[stacks 092J "(2)"]
/-
**Algebra.WeaklyEtale.trans** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.WeaklyEtale`。
形式化陈述：trans (R : Type u₁) (S : Type u₂) [CommRing R] [CommRing S] [Algebra R S] 
(T : Type u₃) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [We
aklyEtale R S] [WeaklyEtale S T] : WeaklyEtale R T
参数：R : Type u₁；S : Type u₂；T : Type u₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.WeaklyEtale.ulift_iff`：ulift_iff : WeaklyEtale (ULift.{u₁} R) (U
Lift.{u₂} S) ↔ WeaklyEtale R S
· 使用定理 `Module.Flat.trans`：trans [Flat R S] [Flat S M] : Flat R M
· 使用定理 `Algebra.WeaklyEtale.flat`：∀ {R : Type u_3} {S : Type u_4} {inst : CommRi
ng R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : Algebra.WeaklyEtale
 R S], Module.…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.lmul'_comp_includeLeft`：∀ {R : Type uR} {S : Type 
uS} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   
(Algebra.TensorProduct.lmul' R).co…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `RingHom.Flat.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg 
: g.Flat) : Flat (g.comp f)
· 使用引理 `RingHom.Flat.mapOfCompatibleSMul`：RingHom.Flat.mapOfCompatibleSMul {R S 
: Type u} (T A : Type u) [CommRing R] [CommRing S] [CommRing T] [CommRing A] [Al
gebra R S] [Algebra R …
· 使用定理 `Algebra.WeaklyEtale.flat_lmul'`：∀ (R : Type u_3) (S : Type u_4) {inst : 
CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : Algebra.Weakl
yEtale R S], (Algebr…
-/
lemma trans (R : Type u₁) (S : Type u₂) [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u₃) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [WeaklyEtale R S] [WeaklyEtale S T] : WeaklyEtale R T := by
  rw [← ulift_iff.{max u₁ u₂ u₃, max u₁ u₂ u₃}] at *
  refine ⟨.trans _ (ULift.{max u₁ u₂ u₃} S) _, ?_⟩
  · have heq : TensorProduct.lmul' (S := ULift.{max u₁ u₂ u₃} T) (ULift R) =
        AlgHom.comp ((TensorProduct.lmul' (S := ULift.{max u₁ u₂ u₃} T)
          (ULift.{max u₁ u₂ u₃} S)).restrictScalars (ULift.{max u₁ u₂ u₃} R))
          (TensorProduct.mapOfCompatibleSMul ..) := by
      ext <;> simp
    rw [heq]
    refine .comp ?_ ?_
    · exact (flat_lmul' (ULift R) (ULift S)).mapOfCompatibleSMul
        (ULift.{max u₁ u₂ u₃} T) (ULift.{max u₁ u₂ u₃} T)
    · exact WeaklyEtale.flat_lmul' (ULift S) (ULift T)

end WeaklyEtale

end Algebra

