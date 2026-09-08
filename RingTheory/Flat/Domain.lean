/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Localization

/-!
# Flat modules in domains

We show that the tensor product of two injective linear maps is injective if the sources are flat
and the ring is an integral domain.
-/

public section

universe u

variable {R M N : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

open TensorProduct Function

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free in
/-- Tensor product of injective maps over domains are injective under some flatness conditions.
Also see `TensorProduct.map_injective_of_flat_flat`
for different flatness conditions but without the domain assumption. -/
/-
**TensorProduct.map_injective_of_flat_flat_of_isDomain** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：TensorProduct.map_injective_of_flat_flat_of_isDomain (f : P ->ₗ[R] M) (g :
 Q ->ₗ[R] N) [H : Module.Flat R P] [Module.Flat R Q] (hf : Injective f) (hg : In
jective g) : Injective (TensorProduct.map f g)
参数：f : P ->ₗ[R] M；g : Q ->ₗ[R] N；hf : Injective f；hg : Injective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `TensorProduct.map_injective_of_flat_flat`：map_injective_of_flat_flat (f 
: P ->ₗ[R] M) (g : Q ->ₗ[R] N) [Module.Flat R M] [Module.Flat R Q] (hf : Functio
n.Injective f) (hg : Function.…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Module.Flat.instTensorProduct`：∀ {R : Type u} {M : Type v} {N : Type u_1
} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : AddCo…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Tensor product of injective maps over domains are injective under some flatness 
conditions.
Also see `TensorProduct.map_injective_of_flat_flat`
for different flatness conditions but without the domain assumption.
-/
lemma TensorProduct.map_injective_of_flat_flat_of_isDomain
    (f : P →ₗ[R] M) (g : Q →ₗ[R] N) [H : Module.Flat R P] [Module.Flat R Q]
    (hf : Injective f) (hg : Injective g) : Injective (TensorProduct.map f g) := by
  let K := FractionRing R
  refine .of_comp (f := TensorProduct.mk R K _ 1) ?_
  have H₁ := TensorProduct.map_injective_of_flat_flat (f.baseChange K) (g.baseChange K)
    (Module.Flat.lTensor_preserves_injective_linearMap f hf)
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)
  have H₂ := (AlgebraTensorModule.cancelBaseChange R K K (K ⊗[R] P) Q).symm.injective
  have H₃ := (AlgebraTensorModule.cancelBaseChange R K K (K ⊗[R] M) N).injective
  have H₄ := (AlgebraTensorModule.assoc R R K K P Q).symm.injective
  have H₅ := (AlgebraTensorModule.assoc R R K K M N).injective
  have H₆ := Module.Flat.rTensor_preserves_injective_linearMap (M := P ⊗[R] Q)
    (Algebra.linearMap R K) (FaithfulSMul.algebraMap_injective R K)
  have H₇ := (TensorProduct.lid R (P ⊗[R] Q)).symm.injective
  convert! H₅.comp <| H₃.comp <| H₁.comp <| H₂.comp <| H₄.comp <| H₆.comp <| H₇
  dsimp only [← LinearMap.coe_comp, ← LinearEquiv.coe_toLinearMap,
    ← @LinearMap.coe_restrictScalars R K]
  congr! 1
  ext p q
  -- `simp` solves the goal but it times out
  change (1 : K) ⊗ₜ[R] (f p ⊗ₜ[R] g q) = (AlgebraTensorModule.assoc R R K K M N)
    (((1 : K) • (algebraMap R K) 1 ⊗ₜ[R] f p) ⊗ₜ[R] g q)
  simp only [map_one, one_smul, AlgebraTensorModule.assoc_tmul]

variable {ι κ : Type*} {v : ι → M} {w : κ → N} {s : Set ι} {t : Set κ}

/-- Tensor product of linearly independent families is linearly independent over domains.
This is true over non-domains if one of the modules is flat.
See `LinearIndependent.tmul_of_flat_left`. -/
/-
**LinearIndependent.tmul_of_isDomain** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.tmul_of_isDomain (hv : LinearIndependent R v) (hw : Line
arIndependent R w) : LinearIndependent R fun i : ι × κ => v i.1 otimesₜ[R] w i.2
参数：hv : LinearIndependent R v；hw : LinearIndependent R w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `finsuppTensorFinsupp'_symm_single_eq_single_one_tmul`：∀ (R : Type u_1) (
ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (i : ι × κ) (r : R),   ((fi
nsuppTensorFinsupp' R ι κ).symm fun₀ | i =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `TensorProduct.map_injective_of_flat_flat_of_isDomain`：TensorProduct.map_
injective_of_flat_flat_of_isDomain (f : P ->ₗ[R] M) (g : Q ->ₗ[R] N) [H : Module
.Flat R P] [Module.Flat R Q] (hf : Injecti…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
Tensor product of linearly independent families is linearly independent over dom
ains.
This is true over non-domains if one of the modules is flat.
See `LinearIndependent.tmul_of_flat_left`.
-/
lemma LinearIndependent.tmul_of_isDomain (hv : LinearIndependent R v) (hw : LinearIndependent R w) :
    LinearIndependent R fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2 := by
  rw [LinearIndependent]
  convert!
    (TensorProduct.map_injective_of_flat_flat_of_isDomain _ _ hv hw).comp
      (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

/-- Tensor product of linearly independent families is linearly independent over domains.
This is true over non-domains if one of the modules is flat.
See `LinearIndepOn.tmul_of_flat_left`. -/
nonrec lemma LinearIndepOn.tmul_of_isDomain (hv : LinearIndepOn R v s) (hw : LinearIndepOn R w t) :
    LinearIndepOn R (fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2) (s ×ˢ t) :=
  ((hv.tmul_of_isDomain hw).comp _ (Equiv.Set.prod _ _).injective :)

