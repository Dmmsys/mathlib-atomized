/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of cotangent spaces

Given an `R`-algebra `S`, an ideal `I` of `S` and a flat `R`-algebra `T`, we show that
the base change `T ⊗[R] I/I²` of the cotangent space of `I` is naturally isomorphic to the
cotangent space of the extended ideal `I · (T ⊗[R] S)`.

## Main definitions

- `Ideal.tensorCotangentHom`: The canonical map `T ⊗[R] I/I² → (I · (T ⊗[R] S))/(I · (T ⊗[R] S))²`.
- `Ideal.tensorCotangentEquiv`: When `T` is `R`-flat, `tensorCotangentHom` is an isomorphism.
-/

@[expose] public noncomputable section

universe u

open TensorProduct

namespace Ideal

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T] (I : Ideal S)

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The canonical map from the base change of the cotangent space `T ⊗[R] I/I²` to the
cotangent space `(I · (T ⊗[R] S))/(I · (T ⊗[R] S))²` of the extended ideal.
This map is always surjective (`tensorCotangentHom_surjective`) and injective
if `T` is `R`-flat (`tensorCotangentHom_injective_of_flat`). -/
/-
**Ideal.tensorCotangentHom** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：tensorCotangentHom : T otimes[R] I.Cotangent ->ₗ[T] (I.map <| (Algebra.Ten
sorProduct.includeRight.toRingHom : S ->+* T otimes[R] S)).Cotangent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the base change of the cotangent space `T ⊗[R] I/I²` to t
he
cotangent space `(I · (T ⊗[R] S))/(I · (T ⊗[R] S))²` of the extended ideal.
This map is always surjective (`tensorCotangentHom_surjective`) and injective
if `T` is `R`-flat (`tensorCotangentHom_injective_of_flat`).
-/
def tensorCotangentHom :
    T ⊗[R] I.Cotangent →ₗ[T]
      (I.map <| (Algebra.TensorProduct.includeRight.toRingHom : S →+* T ⊗[R] S)).Cotangent :=
  LinearMap.liftBaseChange T <|
    Cotangent.lift
      ((map (algebraMap S (T ⊗[R] S)) I).toCotangent.restrictScalars R ∘ₗ
        (Algebra.idealMap _ I).restrictScalars R) <| fun x y ↦ by
    simp only [AlgHom.toRingHom_eq_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, Algebra.idealMap_mul]
    simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, LinearMap.coe_restrictScalars,
      toCotangent_eq_zero, sq, MulMemClass.coe_mul]
    exact mul_mem_mul ((Algebra.idealMap (T ⊗[R] S) I) x).property
      ((Algebra.idealMap (T ⊗[R] S) I) y).property

-- TODO: make this @[simp] when `Ideal.map` is refactored to only take `RingHom`s
/-
**Ideal.tensorCotangentHom_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：tensorCotangentHom_tmul (t : T) (x : I) : tensorCotangentHom R T I (t otim
esₜ[R] I.toCotangent x) = t • (I.map (Algebra.TensorProduct.includeRight.toRingH
om : S ->+* T otimes[R] S)).toCotangent ⟨1 otimesₜ x, Ideal.mem_map_of_mem _ x.2
⟩
参数：t : T；x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma tensorCotangentHom_tmul (t : T) (x : I) :
    tensorCotangentHom R T I (t ⊗ₜ[R] I.toCotangent x) =
      t • (I.map (Algebra.TensorProduct.includeRight.toRingHom : S →+* T ⊗[R] S)).toCotangent
        ⟨1 ⊗ₜ x, Ideal.mem_map_of_mem _ x.2⟩ := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**Ideal.tensorCotangentHom_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：tensorCotangentHom_surjective : Function.Surjective (I.tensorCotangentHom 
R T)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Ideal.map_includeRight_eq`：Ideal.map_includeRight_eq (I : Ideal B) : (I.
map (Algebra.TensorProduct.includeRight : B ->ₐ[R] A otimes[R] B)).restrictScala
rs R = LinearMa…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.cotangentToQuotientSquare_injective`：cotangentToQuotientSquare_inj
ective : Function.Injective I.cotangentToQuotientSquare
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Ideal.tensorCotangentHom_tmul`：tensorCotangentHom_tmul (t : T) (x : I) :
 tensorCotangentHom R T I (t otimesₜ[R] I.toCotangent x) = t • (I.map (Algebra.T
ensorProduct.includ…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Ideal.instIsScalarTowerCotangent`：∀ {R : Type u_3} {S : Type u_1} {S' : 
Type u_2} [inst : CommRing R] [inst_1 : CommSemiring S] [inst_2 : Algebra S R]  
 [inst_3 : CommSemirin…
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
（共 35 条，此处仅展示前 30 条）
-/
lemma tensorCotangentHom_surjective :
    Function.Surjective (I.tensorCotangentHom R T) := by
  let a : S →+* T ⊗[R] S := Algebra.TensorProduct.includeRight.toRingHom
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  obtain ⟨y, rfl⟩ := I.map_includeRight_eq.le hx
  obtain rfl : hx = I.map_includeRight_eq.ge ⟨y, rfl⟩ := rfl
  induction y with
  | zero => exact ⟨0, by simp only [map_zero]; exact (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb]; rfl⟩
  | tmul t x =>
    use t ⊗ₜ I.toCotangent x
    apply Ideal.cotangentToQuotientSquare_injective
    simp [-AlgHom.toRingHom_eq_coe, tensorCotangentHom_tmul, Algebra.smul_def,
      ← Ideal.Quotient.mk_algebraMap, ← map_mul]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `T` is a flat `R`-module, the canonical map `tensorCotangentHom R T I` is injective. -/
/-
**Ideal.tensorCotangentHom_injective_of_flat** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：tensorCotangentHom_injective_of_flat [Module.Flat R T] : Function.Injectiv
e (I.tensorCotangentHom R T)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Ideal.instIsScalarTowerCotangent`：∀ {R : Type u_3} {S : Type u_1} {S' : 
Type u_2} [inst : CommRing R] [inst_1 : CommSemiring S] [inst_2 : Algebra S R]  
 [inst_3 : CommSemirin…
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.tensorCotangentHom_tmul`：tensorCotangentHom_tmul (t : T) (x : I) :
 tensorCotangentHom R T I (t otimesₜ[R] I.toCotangent x) = t • (I.map (Algebra.T
ensorProduct.includ…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Ideal.toCotangent_to_quotient_square`：toCotangent_to_quotient_square (x 
: I) : I.cotangentToQuotientSquare (I.toCotangent x) = (I ^ 2).mkQ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用引理 `Ideal.cotangentToQuotientSquare_injective`：cotangentToQuotientSquare_inj
ective : Function.Injective I.cotangentToQuotientSquare
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g

--- 原说明 ---
If `T` is a flat `R`-module, the canonical map `tensorCotangentHom R T I` is inj
ective.
-/
lemma tensorCotangentHom_injective_of_flat [Module.Flat R T] :
    Function.Injective (I.tensorCotangentHom R T) := by
  let a : S →+* T ⊗[R] S := Algebra.TensorProduct.includeRight.toRingHom
  let f : (I.map a).Cotangent →ₗ[T] T ⊗[R] S ⧸ (I.map a) ^ 2 :=
    (Ideal.cotangentToQuotientSquare _).restrictScalars T
  suffices h : Function.Injective (f ∘ₗ tensorCotangentHom R T I) from .of_comp h
  let g : T ⊗[R] I.Cotangent →ₗ[T] T ⊗[R] (S ⧸ I ^ 2) :=
    AlgebraTensorModule.lTensor T T I.cotangentToQuotientSquare
  let hₐ : T ⊗[R] (S ⧸ I ^ 2) ≃ₐ[T] T ⊗[R] S ⧸ (I.map a) ^ 2 :=
    (Algebra.TensorProduct.tensorQuotientEquiv _ _ _ _).trans
      (Ideal.quotientEquivAlgOfEq T (Ideal.map_pow _ _ _))
  have : f ∘ₗ tensorCotangentHom R T I = hₐ.toLinearMap ∘ₗ g := by
    ext x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    dsimp [f, g, hₐ]
    rw [tensorCotangentHom_tmul, one_smul, Ideal.toCotangent_to_quotient_square]
    simp
  rw [this, LinearMap.coe_comp]
  apply hₐ.injective.comp
  · apply Module.Flat.lTensor_preserves_injective_linearMap (M := T)
      (I.cotangentToQuotientSquare.restrictScalars R)
    apply cotangentToQuotientSquare_injective

/-- If `T` is a flat `R`-module, the base change of the cotangent space of `I` is linearly
equivalent to the cotangent space of the extended ideal `I · (T ⊗[R] S)`. -/
/-
**Ideal.tensorCotangentEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：tensorCotangentEquiv [Module.Flat R T] : T otimes[R] I.Cotangent ≃ₗ[T] (I.
map (Algebra.TensorProduct.includeRight.toRingHom : _ ->+* T otimes[R] S)).Cotan
gent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `T` is a flat `R`-module, the base change of the cotangent space of `I` is li
nearly
equivalent to the cotangent space of the extended ideal `I · (T ⊗[R] S)`.
-/
def tensorCotangentEquiv [Module.Flat R T] :
    T ⊗[R] I.Cotangent ≃ₗ[T]
      (I.map (Algebra.TensorProduct.includeRight.toRingHom : _ →+* T ⊗[R] S)).Cotangent :=
  LinearEquiv.ofBijective (I.tensorCotangentHom R T)
    ⟨I.tensorCotangentHom_injective_of_flat R T, I.tensorCotangentHom_surjective R T⟩

-- TODO: make this @[simp] when `Ideal.map` is refactored to only take `RingHom`s
/-
**Ideal.tensorCotangentEquiv_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：tensorCotangentEquiv_tmul [Module.Flat R T] (t : T) (x : I) : I.tensorCota
ngentEquiv R T (t otimesₜ I.toCotangent x) = t • (I.map (Algebra.TensorProduct.i
ncludeRight.toRingHom : S ->+* T otimes[R] S)).toCotangent ⟨1 otimesₜ x, Ideal.m
em_map_of_mem _ x.2⟩
参数：t : T；x : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma tensorCotangentEquiv_tmul [Module.Flat R T] (t : T) (x : I) :
    I.tensorCotangentEquiv R T (t ⊗ₜ I.toCotangent x) =
      t • (I.map (Algebra.TensorProduct.includeRight.toRingHom : S →+* T ⊗[R] S)).toCotangent
        ⟨1 ⊗ₜ x, Ideal.mem_map_of_mem _ x.2⟩ :=
  rfl

end Ideal

