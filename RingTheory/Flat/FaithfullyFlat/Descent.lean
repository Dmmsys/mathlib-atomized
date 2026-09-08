/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Injective
public import Mathlib.RingTheory.RingHom.Surjective

/-!
# Properties satisfying faithfully flat descent for rings

We show the following properties of ring homomorphisms descend under faithfully flat ring maps:

- injective
- surjective
- bijective
-/

public section

open TensorProduct

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {T : Type*} [CommRing T] [Algebra R T]

/-
**Module.FaithfullyFlat.injective_of_tensorProduct** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.FaithfullyFlat.injective_of_tensorProduct [Module.FaithfullyFlat R 
S] (H : Function.Injective (algebraMap S (S otimes[R] T))) : Function.Injective 
(algebraMap R T)
参数：H : Function.Injective (algebraMap S (S otimes[R] T))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Module.FaithfullyFlat.lTensor_injective_iff_injective`：lTensor_injective
_iff_injective [Module.FaithfullyFlat R M] : Function.Injective (f.lTensor M) ↔ 
Function.Injective f
-/
lemma Module.FaithfullyFlat.injective_of_tensorProduct [Module.FaithfullyFlat R S]
    (H : Function.Injective (algebraMap S (S ⊗[R] T))) :
    Function.Injective (algebraMap R T) := by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S ⊗[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective R S (Algebra.linearMap R T)).mp
  simpa [this] using! H
/-
**Module.FaithfullyFlat.surjective_of_tensorProduct** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：Module.FaithfullyFlat.surjective_of_tensorProduct [Module.FaithfullyFlat R
 S] (H : Function.Surjective (algebraMap S (S otimes[R] T))) : Function.Surjecti
ve (algebraMap R T)
参数：H : Function.Surjective (algebraMap S (S otimes[R] T))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Module.FaithfullyFlat.lTensor_surjective_iff_surjective`：lTensor_surject
ive_iff_surjective [Module.FaithfullyFlat R M] : Function.Surjective (f.lTensor 
M) ↔ Function.Surjective f
-/
lemma Module.FaithfullyFlat.surjective_of_tensorProduct [Module.FaithfullyFlat R S]
    (H : Function.Surjective (algebraMap S (S ⊗[R] T))) :
    Function.Surjective (algebraMap R T) := by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S ⊗[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S (Algebra.linearMap R T)).mp
  simpa [this] using! H
/-
**Module.FaithfullyFlat.bijective_of_tensorProduct** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.FaithfullyFlat.bijective_of_tensorProduct [Module.FaithfullyFlat R 
S] (H : Function.Bijective (algebraMap S (S otimes[R] T))) : Function.Bijective 
(algebraMap R T)
参数：H : Function.Bijective (algebraMap S (S otimes[R] T))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.FaithfullyFlat.injective_of_tensorProduct`：Module.FaithfullyFlat.
injective_of_tensorProduct [Module.FaithfullyFlat R S] (H : Function.Injective (
algebraMap S (S otimes[R] T))) : Funct…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Module.FaithfullyFlat.surjective_of_tensorProduct`：Module.FaithfullyFlat
.surjective_of_tensorProduct [Module.FaithfullyFlat R S] (H : Function.Surjectiv
e (algebraMap S (S otimes[R] T))) : Fun…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Module.FaithfullyFlat.bijective_of_tensorProduct [Module.FaithfullyFlat R S]
    (H : Function.Bijective (algebraMap S (S ⊗[R] T))) :
    Function.Bijective (algebraMap R T) :=
  ⟨injective_of_tensorProduct H.1, surjective_of_tensorProduct H.2⟩

end

/-
**RingHom.FaithfullyFlat.codescendsAlong_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.FaithfullyFlat.codescendsAlong_injective : CodescendsAlong (fun f 
=> Function.Injective f) FaithfullyFlat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.CodescendsAlong.mk`：∀ {P : {R S : Type u} → [inst : CommRing R] 
→ [inst_1 : CommRing S] → (R →+* S) → Prop}   (Q : {R S : Type u} → [inst : Comm
Ring R] → [inst_…
· 使用定理 `RingHom.injective_respectsIso`：RingHom.RespectsIso fun {R S} [CommRing R
] [CommRing S] f => Function.Injective ⇑f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.FaithfullyFlat.injective_of_tensorProduct`：Module.FaithfullyFlat.
injective_of_tensorProduct [Module.FaithfullyFlat R S] (H : Function.Injective (
algebraMap S (S otimes[R] T))) : Funct…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
-/
lemma RingHom.FaithfullyFlat.codescendsAlong_injective :
    CodescendsAlong (fun f ↦ Function.Injective f) FaithfullyFlat := by
  apply CodescendsAlong.mk _ injective_respectsIso
  introv h H
  rw [faithfullyFlat_algebraMap_iff] at h
  exact h.injective_of_tensorProduct H
/-
**RingHom.FaithfullyFlat.codescendsAlong_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：RingHom.FaithfullyFlat.codescendsAlong_surjective : CodescendsAlong (fun f
 => Function.Surjective f) FaithfullyFlat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.CodescendsAlong.mk`：∀ {P : {R S : Type u} → [inst : CommRing R] 
→ [inst_1 : CommRing S] → (R →+* S) → Prop}   (Q : {R S : Type u} → [inst : Comm
Ring R] → [inst_…
· 使用定理 `RingHom.surjective_respectsIso`：surjective_respectsIso : RespectsIso sur
jective
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.FaithfullyFlat.surjective_of_tensorProduct`：Module.FaithfullyFlat
.surjective_of_tensorProduct [Module.FaithfullyFlat R S] (H : Function.Surjectiv
e (algebraMap S (S otimes[R] T))) : Fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
-/
lemma RingHom.FaithfullyFlat.codescendsAlong_surjective :
    CodescendsAlong (fun f ↦ Function.Surjective f) FaithfullyFlat := by
  apply CodescendsAlong.mk _ surjective_respectsIso
  introv h H
  rw [faithfullyFlat_algebraMap_iff] at h
  exact h.surjective_of_tensorProduct H

universe u
/-
**RingHom.FaithfullyFlat.codescendsAlong_bijective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.FaithfullyFlat.codescendsAlong_bijective : CodescendsAlong (fun f 
=> Function.Bijective f) FaithfullyFlat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.CodescendsAlong.and`：∀ {P Q P' : {R S : Type u} → [inst : CommRi
ng R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.CodescendsAlong (f
un {R S} [CommRin…
· 使用引理 `RingHom.FaithfullyFlat.codescendsAlong_injective`：RingHom.FaithfullyFlat
.codescendsAlong_injective : CodescendsAlong (fun f => Function.Injective f) Fai
thfullyFlat
· 使用引理 `RingHom.FaithfullyFlat.codescendsAlong_surjective`：RingHom.FaithfullyFla
t.codescendsAlong_surjective : CodescendsAlong (fun f => Function.Surjective f) 
FaithfullyFlat
-/
lemma RingHom.FaithfullyFlat.codescendsAlong_bijective :
    CodescendsAlong (fun f ↦ Function.Bijective f) FaithfullyFlat :=
  CodescendsAlong.and codescendsAlong_injective codescendsAlong_surjective
