/-
Copyright (c) 2025 Christian Merten, Yi Song, Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Yi Song, Sihan Su
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Properties of faithfully flat algebras

An `A`-algebra `B` is faithfully flat if `B` is faithfully flat as an `A`-module. In this
file we give equivalent characterizations of faithful flatness in the algebra case.

## Main results

Let `B` be a faithfully flat `A`-algebra:

- `Ideal.comap_map_eq_self_of_faithfullyFlat`: the contraction of the extension of any ideal of
  `A` to `B` is the ideal itself.
- `Module.FaithfullyFlat.tensorProduct_mk_injective`: The natural map `M →ₗ[A] B ⊗[A] M` is
  injective for any `A`-module `M`.
- `PrimeSpectrum.comap_surjective_of_faithfullyFlat`: The map on prime spectra induced by
  a faithfully flat ring map is surjective. See also
  `Ideal.exists_isPrime_liesOver_of_faithfullyFlat` for a version stated in terms of
  `Ideal.LiesOver`.

Conversely, let `B` be a flat `A`-algebra:

- `Module.FaithfullyFlat.of_comap_surjective`: `B` is faithfully flat over `A`,
  if the induced map on prime spectra is surjective.
- `Module.FaithfullyFlat.of_flat_of_isLocalHom`: flat + local implies faithfully flat

-/

public section

universe u v

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

open TensorProduct LinearMap

/-- If `A →+* B` is flat and surjective on prime spectra, `B` is a faithfully flat `A`-algebra. -/
/-
**Module.FaithfullyFlat.of_comap_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.FaithfullyFlat.of_comap_surjective [Flat A B] (h : Function.Surject
ive (PrimeSpectrum.comap (algebraMap A B))) : Module.FaithfullyFlat A B
参数：h : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.comap_asIdeal`：comap_asIdeal (y : PrimeSpectrum S) : (coma
p f y).asIdeal = Ideal.comap f y.asIdeal
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Submodule.restrictScalars_eq_top_iff`：restrictScalars_eq_top_iff {p : Su
bmodule R M} : restrictScalars S p = ⊤ ↔ p = ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K

--- 原说明 ---
If `A →+* B` is flat and surjective on prime spectra, `B` is a faithfully flat `
A`-algebra.
-/
lemma Module.FaithfullyFlat.of_comap_surjective [Flat A B]
    (h : Function.Surjective (PrimeSpectrum.comap (algebraMap A B))) :
    Module.FaithfullyFlat A B := by
  refine ⟨fun m hm ↦ ?_⟩
  obtain ⟨m', hm'⟩ := h ⟨m, hm.isPrime⟩
  have : m = Ideal.comap (algebraMap A B) m'.asIdeal := by
    rw [← PrimeSpectrum.comap_asIdeal (algebraMap A B) m', hm']
  rw [Ideal.smul_top_eq_map, this]
  exact (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr
    fun top ↦ m'.isPrime.ne_top <| top_le_iff.mp <| top ▸ Ideal.map_comap_le

/-- If `A` is local and `B` is a local and flat `A`-algebra, then `B` is faithfully flat. -/
/-
**Module.FaithfullyFlat.of_flat_of_isLocalHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.FaithfullyFlat.of_flat_of_isLocalHom [IsLocalRing A] [IsLocalRing B
] [Flat A B] [IsLocalHom (algebraMap A B)] : Module.FaithfullyFlat A B
参数：algebraMap A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocalRing.local_hom_TFAE`：local_hom_TFAE (f : R ->+* S) : List.TFAE [I
sLocalHom f, f '' maximalIdeal R subseteq maximalIdeal S, (maximalIdeal R).map f
 <= maximalIdeal…
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Submodule.restrictScalars_eq_top_iff`：restrictScalars_eq_top_iff {p : Su
bmodule R M} : restrictScalars S p = ⊤ ↔ p = ⊤
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤

--- 原说明 ---
If `A` is local and `B` is a local and flat `A`-algebra, then `B` is faithfully 
flat.
-/
lemma Module.FaithfullyFlat.of_flat_of_isLocalHom [IsLocalRing A] [IsLocalRing B] [Flat A B]
    [IsLocalHom (algebraMap A B)] : Module.FaithfullyFlat A B := by
  refine ⟨fun m hm ↦ ?_⟩
  rw [Ideal.smul_top_eq_map, IsLocalRing.eq_maximalIdeal hm]
  by_contra eqt
  have : Submodule.restrictScalars A (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) ≤
      Submodule.restrictScalars A (IsLocalRing.maximalIdeal B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 0 2).mp ‹_›
  rw [eqt, top_le_iff, Submodule.restrictScalars_eq_top_iff] at this
  exact Ideal.IsPrime.ne_top' this
/-
**Module.FaithfullyFlat.of_isIntegral_of_isDomain** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.FaithfullyFlat.of_isIntegral_of_isDomain [IsDomain B] [Module.Flat 
A B] [Algebra.IsIntegral A B] [FaithfulSMul A B] : Module.FaithfullyFlat A B
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.FaithfullyFlat.of_comap_surjective`：Module.FaithfullyFlat.of_coma
p_surjective [Flat A B] (h : Function.Surjective (PrimeSpectrum.comap (algebraMa
p A B))) : Module.FaithfullyFla…
· 使用定理 `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain`：exists_ideal_ov
er_prime_of_isIntegral_of_isDomain [Algebra.IsIntegral R S] (P : Ideal R) [IsPri
me P] (hP : RingHom.ker (algebraMap R S) <= P…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.ext_iff`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : P
rimeSpectrum R}, x = y ↔ x.asIdeal = y.asIdeal
-/
instance Module.FaithfullyFlat.of_isIntegral_of_isDomain [IsDomain B] [Module.Flat A B]
    [Algebra.IsIntegral A B] [FaithfulSMul A B] :
    Module.FaithfullyFlat A B := by
  refine Module.FaithfullyFlat.of_comap_surjective fun P ↦ ?_
  obtain ⟨P, hP₁, hP₂⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain P.1 (S := B)
    (by simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)])
  exact ⟨⟨P, hP₁⟩, PrimeSpectrum.ext_iff.mpr hP₂⟩

variable [Module.FaithfullyFlat A B]

/-- If `B` is a faithfully flat `A`-module and `M` is any `A`-module, the canonical
map `M →ₗ[A] B ⊗[A] M` is injective.

See also `Module.Flat.tensorProduct_mk_injective`. -/
/-
**Module.FaithfullyFlat.tensorProduct_mk_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.FaithfullyFlat.tensorProduct_mk_injective (M : Type*) [AddCommGroup
 M] [Module A M] : Function.Injective (TensorProduct.mk A B M 1)
参数：M : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.FaithfullyFlat.lTensor_injective_iff_injective`：lTensor_injective
_iff_injective [Module.FaithfullyFlat R M] : Function.Injective (f.lTensor M) ↔ 
Function.Injective f
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `EmbeddingLike.comp_injective`：comp_injective {F : Sort*} [FunLike F β γ]
 [EmbeddingLike F β γ] (f : α -> β) (e : F) : Function.Injective (e ∘ f) ↔ Funct
ion.Injective f
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `Algebra.TensorProduct.mk_one_injective_of_isScalarTower`：mk_one_injectiv
e_of_isScalarTower (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsSc
alarTower R S M] : Function.Injective (Tensor…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If `B` is a faithfully flat `A`-module and `M` is any `A`-module, the canonical
map `M →ₗ[A] B ⊗[A] M` is injective.

See also `Module.Flat.tensorProduct_mk_injective`.
-/
lemma Module.FaithfullyFlat.tensorProduct_mk_injective (M : Type*) [AddCommGroup M] [Module A M] :
    Function.Injective (TensorProduct.mk A B M 1) := by
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective A B]
  have : (lTensor B <| TensorProduct.mk A B M 1) =
      (TensorProduct.leftComm A B B M).symm.comp (TensorProduct.mk A B (B ⊗[A] M) 1) := by
    apply TensorProduct.ext'
    intro x y
    simp
  rw [this, coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective]
  exact Algebra.TensorProduct.mk_one_injective_of_isScalarTower _
/-
**Module.FaithfullyFlat.faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.FaithfullyFlat.faithfulSMul : FaithfulSMul A B
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.FaithfullyFlat.tensorProduct_mk_injective`：Module.FaithfullyFlat.
tensorProduct_mk_injective (M : Type*) [AddCommGroup M] [Module A M] : Function.
Injective (TensorProduct.mk A B M 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Module.FaithfullyFlat.faithfulSMul : FaithfulSMul A B := by
  constructor
  intro a₁ a₂ ha
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) A
  simp only [TensorProduct.mk_apply]
  rw [← mul_one a₁, ← mul_one a₂]
  simp only [← smul_eq_mul, ← TensorProduct.smul_tmul, ha (1 : B)]

open Algebra.TensorProduct in
/-- If `B` is a faithfully flat `A`-algebra, the preimage of the pushforward of any
ideal `I` is again `I`. -/
/-
**Ideal.comap_map_eq_self_of_faithfullyFlat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.comap_map_eq_self_of_faithfullyFlat (I : Ideal A) : (I.map (algebraM
ap A B)).comap (algebraMap A B) = I
参数：I : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `AlgEquiv.toLinearMap.eq_1`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA
₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst
_3 : Algebra R …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.restrictScalars_toLinearMap`：∀ (R : Type u_1) {S : Type u_4}
 {M : Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [ins
t_2 : AddCommMonoid M] [inst_…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用引理 `Module.FaithfullyFlat.tensorProduct_mk_injective`：Module.FaithfullyFlat.
tensorProduct_mk_injective (M : Type*) [AddCommGroup M] [Module A M] : Function.
Injective (TensorProduct.mk A B M 1)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f

--- 原说明 ---
If `B` is a faithfully flat `A`-algebra, the preimage of the pushforward of any
ideal `I` is again `I`.
-/
lemma Ideal.comap_map_eq_self_of_faithfullyFlat (I : Ideal A) :
    (I.map (algebraMap A B)).comap (algebraMap A B) = I := by
  refine le_antisymm ?_ le_comap_map
  have inj : Function.Injective
      ((quotIdealMapEquivTensorQuot B I).symm.toLinearMap.restrictScalars _ ∘ₗ
        TensorProduct.mk A B (A ⧸ I) 1) := by
    rw [LinearMap.coe_comp, AlgEquiv.toLinearMap, ← LinearEquiv.restrictScalars_toLinearMap]
    exact (LinearEquiv.injective _).comp <|
      Module.FaithfullyFlat.tensorProduct_mk_injective (A ⧸ I)
  intro x hx
  rw [Ideal.mem_comap] at hx
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  apply inj
  have : ((quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv.toLinearMap.restrictScalars _ ∘ₗ
      TensorProduct.mk A B (A ⧸ I) 1) x = 0 := by
    simp [← Algebra.algebraMap_eq_smul_one, hx]
  simp [this]

/-- If `B` is a faithfully-flat `A`-algebra, every ideal in `A` is the preimage of some ideal
in `B`. -/
/-
**Ideal.comap_surjective_of_faithfullyFlat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.comap_surjective_of_faithfullyFlat : Function.Surjective (Ideal.coma
p (algebraMap A B))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.comap_map_eq_self_of_faithfullyFlat`：Ideal.comap_map_eq_self_of_fa
ithfullyFlat (I : Ideal A) : (I.map (algebraMap A B)).comap (algebraMap A B) = I

--- 原说明 ---
If `B` is a faithfully-flat `A`-algebra, every ideal in `A` is the preimage of s
ome ideal
in `B`.
-/
lemma Ideal.comap_surjective_of_faithfullyFlat :
    Function.Surjective (Ideal.comap (algebraMap A B)) :=
  fun I ↦ ⟨I.map (algebraMap A B), comap_map_eq_self_of_faithfullyFlat I⟩

/-- If `B` is a faithfully-flat `A`-algebra, the lifting an ideal in `A` to `B` is injective. -/
/-
**Ideal.map_injective_of_faithfullyFlat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.map_injective_of_faithfullyFlat : Function.Injective (map (algebraMa
p A B))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.comap_map_eq_self_of_faithfullyFlat`：Ideal.comap_map_eq_self_of_fa
ithfullyFlat (I : Ideal A) : (I.map (algebraMap A B)).comap (algebraMap A B) = I
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If `B` is a faithfully-flat `A`-algebra, the lifting an ideal in `A` to `B` is i
njective.
-/
lemma Ideal.map_injective_of_faithfullyFlat :
    Function.Injective (map (algebraMap A B)) :=
  fun _ _ h ↦ by simpa [comap_map_eq_self_of_faithfullyFlat]
    using congr_arg (Ideal.comap (algebraMap A B) ·) h

/-- If `B` is faithfully flat over `A`, every prime of `A` comes from a prime of `B`. -/
/-
**Ideal.exists_isPrime_liesOver_of_faithfullyFlat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.exists_isPrime_liesOver_of_faithfullyFlat (p : Ideal A) [p.IsPrime] 
: exists (P : Ideal B), P.IsPrime ∧ P.LiesOver p
参数：p : Ideal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Ideal.comap_map_eq_self_iff_of_isPrime`：comap_map_eq_self_iff_of_isPrime
 {S : Type*} [CommSemiring S] {f : R ->+* S} (p : Ideal R) [p.IsPrime] : (p.map 
f).comap f = p ↔ (exists (q …
· 使用引理 `Ideal.comap_map_eq_self_of_faithfullyFlat`：Ideal.comap_map_eq_self_of_fa
ithfullyFlat (I : Ideal A) : (I.map (algebraMap A B)).comap (algebraMap A B) = I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `B` is faithfully flat over `A`, every prime of `A` comes from a prime of `B`
.
-/
lemma Ideal.exists_isPrime_liesOver_of_faithfullyFlat (p : Ideal A) [p.IsPrime] :
    ∃ (P : Ideal B), P.IsPrime ∧ P.LiesOver p := by
  obtain ⟨P, _, hP⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime p).mp <|
    p.comap_map_eq_self_of_faithfullyFlat (B := B)
  exact ⟨P, inferInstance, ⟨hP.symm⟩⟩

/-- If `B` is a faithfully flat `A`-algebra, the induced map on the prime spectrum is
surjective. -/
/-
**PrimeSpectrum.comap_surjective_of_faithfullyFlat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrimeSpectrum.comap_surjective_of_faithfullyFlat : Function.Surjective (co
map (algebraMap A B))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PrimeSpectrum.mem_range_comap_iff`：PrimeSpectrum.mem_range_comap_iff {p 
: PrimeSpectrum R} : p in Set.range (comap f) ↔ (p.asIdeal.map f).comap f = p.as
Ideal
· 使用引理 `Ideal.comap_map_eq_self_of_faithfullyFlat`：Ideal.comap_map_eq_self_of_fa
ithfullyFlat (I : Ideal A) : (I.map (algebraMap A B)).comap (algebraMap A B) = I

--- 原说明 ---
If `B` is a faithfully flat `A`-algebra, the induced map on the prime spectrum i
s
surjective.
-/
lemma PrimeSpectrum.comap_surjective_of_faithfullyFlat :
    Function.Surjective (comap (algebraMap A B)) := fun I ↦
  (PrimeSpectrum.mem_range_comap_iff (algebraMap A B)).mpr
    I.asIdeal.comap_map_eq_self_of_faithfullyFlat

section IsLocalRing

variable (A B)

/-
**Module.FaithfullyFlat.isLocalHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.FaithfullyFlat.isLocalHom : IsLocalHom (algebraMap A B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHom.of_comap_surjective`：IsLocalHom.of_comap_surjective [CommSemi
ring R] [CommSemiring S] (f : R ->+* S) (hf : Function.Surjective (comap f)) : I
sLocalHom f where ma…
· 使用引理 `PrimeSpectrum.comap_surjective_of_faithfullyFlat`：PrimeSpectrum.comap_su
rjective_of_faithfullyFlat : Function.Surjective (comap (algebraMap A B))
-/
instance Module.FaithfullyFlat.isLocalHom : IsLocalHom (algebraMap A B) :=
  IsLocalHom.of_comap_surjective (algebraMap A B) PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- Let `B` be a faithfully flat `A`-algebra, then `A` is a local ring if `B` is. -/
/-
**Module.FaithfullyFlat.isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.FaithfullyFlat.isLocalRing [IsLocalRing B] : IsLocalRing A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_isLocalRing`：RingHom.domain_isLocalRing [IsLocalRing S] (
f : R ->+* S) [IsLocalHom f] : IsLocalRing R where toNontrivial

--- 原说明 ---
Let `B` be a faithfully flat `A`-algebra, then `A` is a local ring if `B` is.
-/
theorem Module.FaithfullyFlat.isLocalRing [IsLocalRing B] : IsLocalRing A :=
  (algebraMap A B).domain_isLocalRing

end IsLocalRing

