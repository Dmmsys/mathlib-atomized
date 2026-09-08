/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Filippo A. E. Nuccio, Andrew Yang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Functoriality of the prime spectrum

In this file we define the induced map on prime spectra induced by a ring homomorphism.

## Main definitions

* `PrimeSpectrum.comap`: The induced map on prime spectra by a ring homomorphism. The proof that
  it is continuous is in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

-/

@[expose] public section

universe u v

variable (R : Type u) (S : Type v)

open PrimeSpectrum

/-- The pullback of an element of `PrimeSpectrum S` along a ring homomorphism `f : R →+* S`.
The bundled continuous version is `PrimeSpectrum.comap`. -/
/-
**PrimeSpectrum.comap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PrimeSpectrum.comap {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R
 ->+* S) (p : PrimeSpectrum S) : PrimeSpectrum R
参数：f : R ->+* S；p : PrimeSpectrum S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of an element of `PrimeSpectrum S` along a ring homomorphism `f : R
 →+* S`.
The bundled continuous version is `PrimeSpectrum.comap`.
-/
def PrimeSpectrum.comap {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : PrimeSpectrum S) : PrimeSpectrum R :=
  ⟨Ideal.comap f p.asIdeal, inferInstance⟩

namespace PrimeSpectrum

open RingHom

variable {R S} {S' : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring S']

variable (f : R →+* S)

@[simp]
/-
**PrimeSpectrum.comap_asIdeal** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：comap_asIdeal (y : PrimeSpectrum S) : (comap f y).asIdeal = Ideal.comap f 
y.asIdeal
参数：y : PrimeSpectrum S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_asIdeal (y : PrimeSpectrum S) :
    (comap f y).asIdeal = Ideal.comap f y.asIdeal :=
  rfl

@[simp]
/-
**PrimeSpectrum.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：comap_id : comap (RingHom.id R) = fun x => x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id : comap (RingHom.id R) = fun x => x :=
  rfl

@[simp]
/-
**PrimeSpectrum.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：comap_comp (f : R ->+* S) (g : S ->+* S') : comap (g.comp f) = (comap f).c
omp (comap g)
参数：f : R ->+* S；g : S ->+* S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comp (f : R →+* S) (g : S →+* S') :
    comap (g.comp f) = (comap f).comp (comap g) :=
  rfl
/-
**PrimeSpectrum.comap_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：comap_comp_apply (f : R ->+* S) (g : S ->+* S') (x : PrimeSpectrum S') : c
omap (g.comp f) x = comap f (comap g x)
参数：f : R ->+* S；g : S ->+* S'；x : PrimeSpectrum S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comp_apply (f : R →+* S) (g : S →+* S') (x : PrimeSpectrum S') :
    comap (g.comp f) x = comap f (comap g x) :=
  rfl
/-
**PrimeSpectrum.preimage_comap_zeroLocus_aux** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpe
ctrum`。
形式化陈述：preimage_comap_zeroLocus_aux (f : R ->+* S) (s : Set R) : comap f ⁻¹' zero
Locus s = zeroLocus (f '' s)
参数：f : R ->+* S；s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_comap_zeroLocus_aux (f : R →+* S) (s : Set R) :
    comap f ⁻¹' zeroLocus s = zeroLocus (f '' s) := by
  ext x
  simp [mem_zeroLocus, Set.image_subset_iff, Set.mem_preimage, mem_zeroLocus]

@[simp]
/-
**PrimeSpectrum.preimage_comap_zeroLocus** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectru
m`。
形式化陈述：preimage_comap_zeroLocus (s : Set R) : comap f ⁻¹' zeroLocus s = zeroLocus
 (f '' s)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.preimage_comap_zeroLocus_aux`：preimage_comap_zeroLocus_aux
 (f : R ->+* S) (s : Set R) : comap f ⁻¹' zeroLocus s = zeroLocus (f '' s)
-/
theorem preimage_comap_zeroLocus (s : Set R) :
    comap f ⁻¹' zeroLocus s = zeroLocus (f '' s) :=
  preimage_comap_zeroLocus_aux f s
/-
**PrimeSpectrum.comap_injective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSp
ectrum`。
形式化陈述：comap_injective_of_surjective (f : R ->+* S) (hf : Function.Surjective f) 
: Function.Injective (comap f)
参数：f : R ->+* S；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.comap_injective_of_surjective`：comap_injective_of_surjective : Inj
ective (comap f)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem comap_injective_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective (comap f) := fun x y h =>
  PrimeSpectrum.ext
    (Ideal.comap_injective_of_surjective f hf
      (congr_arg PrimeSpectrum.asIdeal h : (comap f x).asIdeal = (comap f y).asIdeal))
/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra R S] (p : PrimeSpectrum S) :
    p.asIdeal.LiesOver (p.comap <| algebraMap R S).asIdeal where
  over := rfl

/-- `RingHom.comap` of an isomorphism of rings as an equivalence of their prime spectra. -/
@[simps apply]
/-
**PrimeSpectrum.comapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：comapEquiv (e : R ≃+* S) : PrimeSpectrum R ≃o PrimeSpectrum S where toFun
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RingHom.comap` of an isomorphism of rings as an equivalence of their prime spec
tra.
-/
def comapEquiv (e : R ≃+* S) : PrimeSpectrum R ≃o PrimeSpectrum S where
  toFun := comap e.symm.toRingHom
  invFun := comap e.toRingHom
  left_inv x := by
    rw [← comap_comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp]
    rfl
  right_inv x := by
    rw [← comap_comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingEquiv.comp_symm]
    rfl
  map_rel_iff' {I J} := Ideal.comap_le_comap_iff_of_surjective _ e.symm.surjective ..
/-
**PrimeSpectrum.comapEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : CommSemiring
 S] (e : R ≃+* S),   (PrimeSpectrum.comapEquiv e).symm = PrimeSpectrum.comapEqui
v e.symm
参数：e : R ≃+* S；PrimeSpectrum.comapEquiv e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comapEquiv_symm (e : R ≃+* S) : (comapEquiv e).symm = comapEquiv e.symm := rfl

section Pi

variable {ι} (R : ι → Type*) [∀ i, CommSemiring (R i)]

/--
The canonical map from a disjoint union of prime spectra of commutative semirings to
the prime spectrum of the product semiring.
This is always an open embedding, see `PrimeSpectrum.isOpenEmbedding_sigmaToPi` and
a homeomorphism if `ι` is finite, see `PrimeSpectrum.sigmaHomeoPi`.
-/
/-
**PrimeSpectrum.sigmaToPi** 是 Mathlib 中的一个定义，位于命名空间 `PrimeSpectrum`。
形式化陈述：{ι : Type u_3} →   (R : ι → Type u_2) →     [inst : (i : ι) → CommSemiring
 (R i)] → (i : ι) × PrimeSpectrum (R i) → PrimeSpectrum ((i : ι) → R i)
参数：R : ι → Type u_2；i : ι；R i；i : ι；R i；(i : ι) → R i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from a disjoint union of prime spectra of commutative semiring
s to
the prime spectrum of the product semiring.
This is always an open embedding, see `PrimeSpectrum.isOpenEmbedding_sigmaToPi` 
and
a homeomorphism if `ι` is finite, see `PrimeSpectrum.sigmaHomeoPi`.
-/
def sigmaToPi : (Σ i, PrimeSpectrum (R i)) → PrimeSpectrum (Π i, R i)
  | ⟨i, p⟩ => comap (Pi.evalRingHom R i) p

@[simp]
/-
**PrimeSpectrum.sigmaToPi_apply** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：sigmaToPi_apply (i : ι) (p : PrimeSpectrum (R i)) : sigmaToPi R ⟨i, p⟩ = c
omap (Pi.evalRingHom R i) p
参数：i : ι；p : PrimeSpectrum (R i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sigmaToPi_apply (i : ι) (p : PrimeSpectrum (R i)) :
    sigmaToPi R ⟨i, p⟩ = comap (Pi.evalRingHom R i) p :=
  rfl

@[deprecated (since := "2026-04-17")]
alias coe_sigmaToPi_asIdeal := sigmaToPi_apply
/-
**PrimeSpectrum.sigmaToPi_injective** 是 Mathlib 中的一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：sigmaToPi_injective : (sigmaToPi R).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.evalRingHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) → 
NonAssocSemiring (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalRingHom f i) g = 
g i
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem sigmaToPi_injective : (sigmaToPi R).Injective := fun ⟨i, p⟩ ⟨j, q⟩ eq ↦ by
  classical
  obtain rfl | ne := eq_or_ne i j
  · congr; ext x
    simpa using congr_arg (Function.update (0 : ∀ i, R i) i x ∈ ·.asIdeal) eq
  · refine (p.1.ne_top_iff_one.mp p.2.ne_top ?_).elim
    have : Function.update (1 : ∀ i, R i) j 0 ∈ (sigmaToPi R ⟨j, q⟩).asIdeal := by simp
    simpa [← eq, Function.update_of_ne ne]

variable [Infinite ι] [∀ i, Nontrivial (R i)]

/-- An infinite product of nontrivial commutative semirings has a maximal ideal outside of the
range of `sigmaToPi`, i.e. is not of the form `πᵢ⁻¹(𝔭)` for some prime `𝔭 ⊂ R i`, where
`πᵢ : (Π i, R i) →+* R i` is the projection. For a complete description of all prime ideals,
see https://math.stackexchange.com/a/1563190. -/
/-
**PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite** 是 Mathlib 中的
一个定理，位于命名空间 `PrimeSpectrum`。
形式化陈述：exists_maximal_notMem_range_sigmaToPi_of_infinite : exists (I : Ideal (Π i
, R i)) (_ : I.IsMaximal), ⟨I, inferInstance⟩ ∉ Set.range (sigmaToPi R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dite_eq_left_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x : 
α} {y : ¬p → α},   (if h : p then x else y h) = x ↔ ∀ (h : ¬p), y h = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.notMem_support_iff`：notMem_support_iff {f : Π₀ i, β i} {i : ι} 
: i ∉ f.support ↔ f i = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `Finset.exists_notMem`：∀ {α : Type u} [Infinite α] (s : Finset α), ∃ a, a
 ∉ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.evalRingHom_apply`：∀ {I : Type u} (f : I → Type v) [inst : (i : I) → 
NonAssocSemiring (f i)] (i : I) (g : (i : I) → f i),   (Pi.evalRingHom f i) g = 
g i
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime

--- 原说明 ---
An infinite product of nontrivial commutative semirings has a maximal ideal outs
ide of the
range of `sigmaToPi`, i.e. is not of the form `πᵢ⁻¹(𝔭)` for some prime `𝔭 ⊂ R i`
, where
`πᵢ : (Π i, R i) →+* R i` is the projection. For a complete description of all p
rime ideals,
see https://math.stackexchange.com/a/1563190.
-/
theorem exists_maximal_notMem_range_sigmaToPi_of_infinite :
    ∃ (I : Ideal (Π i, R i)) (_ : I.IsMaximal), ⟨I, inferInstance⟩ ∉ Set.range (sigmaToPi R) := by
  classical
  let J : Ideal (Π i, R i) := -- `J := Π₀ i, R i` is an ideal in `Π i, R i`
  { __ := AddMonoidHom.mrange DFinsupp.coeFnAddMonoidHom
    smul_mem' := by
      rintro r _ ⟨x, rfl⟩
      refine ⟨.mk x.support fun i ↦ r i * x i, funext fun i ↦ show dite _ _ _ = _ from ?_⟩
      simp_rw +instances [DFinsupp.coeFnAddMonoidHom]
      refine dite_eq_left_iff.mpr fun h ↦ ?_
      rw [DFinsupp.notMem_support_iff.mp h, mul_zero] }
  have ⟨I, max, le⟩ := J.exists_le_maximal <| (Ideal.ne_top_iff_one _).mpr <| by
    -- take a maximal ideal I containing J
    rintro ⟨x, hx⟩
    have ⟨i, hi⟩ := x.support.exists_notMem
    simpa [DFinsupp.coeFnAddMonoidHom, DFinsupp.notMem_support_iff.mp hi] using congr_fun hx i
  refine ⟨I, max, fun ⟨⟨i, p⟩, eq⟩ ↦ ?_⟩
  -- then I is not in the range of `sigmaToPi`
  have : ⇑(DFinsupp.single i 1) ∉ (sigmaToPi R ⟨i, p⟩).asIdeal := by
    simpa using p.1.ne_top_iff_one.mp p.2.ne_top
  rw [eq] at this
  exact this (le ⟨.single i 1, rfl⟩)
/-
**PrimeSpectrum.sigmaToPi_not_surjective_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `
PrimeSpectrum`。
形式化陈述：sigmaToPi_not_surjective_of_infinite : ¬ (sigmaToPi R).Surjective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite`：exists_
maximal_notMem_range_sigmaToPi_of_infinite : exists (I : Ideal (Π i, R i)) (_ : 
I.IsMaximal), ⟨I, inferInstance⟩ ∉ Set.range (sigmaTo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
-/
theorem sigmaToPi_not_surjective_of_infinite : ¬ (sigmaToPi R).Surjective := fun surj ↦
  have ⟨_, _, notMem⟩ := exists_maximal_notMem_range_sigmaToPi_of_infinite R
  (Set.range_eq_univ.mpr surj ▸ notMem) ⟨⟩
/-
**PrimeSpectrum.exists_comap_evalRingHom_eq** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpec
trum`。
形式化陈述：exists_comap_evalRingHom_eq {ι : Type*} {R : ι -> Type*} [forall i, CommRi
ng (R i)] [Finite ι] (p : PrimeSpectrum (Π i, R i)) : exists (i : ι) (q : PrimeS
pectrum (R i)), comap (Pi.evalRingHom R i) q = p
参数：R i；p : PrimeSpectrum (Π i, R i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `RingHomSurjective.is_surjective`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {inst
 : Semiring R₁} {inst_1 : Semiring R₂} {σ : R₁ →+* R₂}   [self : RingHomSurjecti
ve σ], Function.Surje…
· 使用定理 `instRingHomSurjectiveForallEvalRingHom`：∀ {I : Type u} (f : I → Type u_1
) [inst : (i : I) → Semiring (f i)] (i : I), RingHomSurjective (Pi.evalRingHom f
 i)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Ideal.map_isPrime_of_surjective`：map_isPrime_of_surjective {f : F} (hf :
 Function.Surjective f) {I : Ideal R} [H : IsPrime I] (hk : RingHom.ker f <= I) 
: IsPrime (map f I)
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
-/
lemma exists_comap_evalRingHom_eq
    {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] [Finite ι]
    (p : PrimeSpectrum (Π i, R i)) :
    ∃ (i : ι) (q : PrimeSpectrum (R i)), comap (Pi.evalRingHom R i) q = p := by
  classical
  cases nonempty_fintype ι
  let e (i) : Π i, R i := Function.update 1 i 0
  have H : ∏ i, e i = 0 := by
    ext j
    rw [Finset.prod_apply, Pi.zero_apply, Finset.prod_eq_zero (Finset.mem_univ j)]
    simp [e]
  obtain ⟨i, hi⟩ : ∃ i, e i ∈ p.asIdeal := by
    simpa [← H, Ideal.IsPrime.prod_mem_iff] using p.asIdeal.zero_mem
  let h₁ : Function.Surjective (Pi.evalRingHom R i) := RingHomSurjective.is_surjective
  have h₂ : RingHom.ker (Pi.evalRingHom R i) ≤ p.asIdeal := by
    intro x hx
    convert! p.asIdeal.mul_mem_left x hi
    ext j
    by_cases hj : i = j
    · subst hj; simpa [e]
    · simp [e, Function.update_of_ne (.symm hj)]
  have : (p.asIdeal.map (Pi.evalRingHom R i)).comap (Pi.evalRingHom R i) = p.asIdeal := by
    rwa [Ideal.comap_map_of_surjective _ h₁, sup_eq_left]
  exact ⟨i, ⟨_, Ideal.map_isPrime_of_surjective h₁ h₂⟩, PrimeSpectrum.ext this⟩
/-
**PrimeSpectrum.sigmaToPi_bijective** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`。
形式化陈述：sigmaToPi_bijective {ι : Type*} (R : ι -> Type*) [forall i, CommRing (R i)
] [Finite ι] : Function.Bijective (sigmaToPi R)
参数：R : ι -> Type*；R i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.sigmaToPi_injective`：sigmaToPi_injective : (sigmaToPi R).I
njective
· 使用引理 `PrimeSpectrum.exists_comap_evalRingHom_eq`：exists_comap_evalRingHom_eq {
ι : Type*} {R : ι -> Type*} [forall i, CommRing (R i)] [Finite ι] (p : PrimeSpec
trum (Π i, R i)) : exists (i : …
-/
lemma sigmaToPi_bijective {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] [Finite ι] :
    Function.Bijective (sigmaToPi R) := by
  refine ⟨sigmaToPi_injective R, ?_⟩
  intro q
  obtain ⟨i, q, rfl⟩ := exists_comap_evalRingHom_eq q
  exact ⟨⟨i, q⟩, rfl⟩
/-
**PrimeSpectrum.iUnion_range_comap_comp_evalRingHom** 是 Mathlib 中的一个引理，位于命名空间 `P
rimeSpectrum`。
形式化陈述：iUnion_range_comap_comp_evalRingHom {ι : Type*} {R : ι -> Type*} [forall i
, CommRing (R i)] [Finite ι] {S : Type*} [CommRing S] (f : S ->+* Π i, R i) : ⋃ 
i, Set.range (comap ((Pi.evalRingHom R i).comp f)) = Set.range (comap f)
参数：R i；f : S ->+* Π i, R i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用引理 `PrimeSpectrum.exists_comap_evalRingHom_eq`：exists_comap_evalRingHom_eq {
ι : Type*} {R : ι -> Type*} [forall i, CommRing (R i)] [Finite ι] (p : PrimeSpec
trum (Π i, R i)) : exists (i : …
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
-/
lemma iUnion_range_comap_comp_evalRingHom
    {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] [Finite ι]
    {S : Type*} [CommRing S] (f : S →+* Π i, R i) :
    ⋃ i, Set.range (comap ((Pi.evalRingHom R i).comp f)) = Set.range (comap f) := by
  simp_rw [comap_comp]
  apply subset_antisymm
  · exact Set.iUnion_subset fun _ ↦ Set.range_comp_subset_range _ _
  · rintro _ ⟨p, rfl⟩
    obtain ⟨i, p, rfl⟩ := exists_comap_evalRingHom_eq p
    exact Set.mem_iUnion_of_mem i ⟨p, rfl⟩

end Pi

end PrimeSpectrum

section SpecOfSurjective

open Function RingHom

variable [CommRing R] [CommRing S]
variable (f : R →+* S)
variable {R}

/-
**image_comap_zeroLocus_eq_zeroLocus_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_comap_zeroLocus_eq_zeroLocus_comap (hf : Surjective f) (I : Ideal S)
 : comap f '' zeroLocus I = zeroLocus (I.comap f)
参数：hf : Surjective f；I : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Ideal.map_isPrime_of_surjective`：map_isPrime_of_surjective {f : F} (hf :
 Function.Surjective f) {I : Ideal R} [H : IsPrime I] (hk : RingHom.ker f <= I) 
: IsPrime (map f I)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `PrimeSpectrum.comap_asIdeal`：comap_asIdeal (y : PrimeSpectrum S) : (coma
p f y).asIdeal = Ideal.comap f y.asIdeal
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
theorem image_comap_zeroLocus_eq_zeroLocus_comap (hf : Surjective f) (I : Ideal S) :
    comap f '' zeroLocus I = zeroLocus (I.comap f) := by
  simp only [Set.ext_iff, Set.mem_image, mem_zeroLocus, SetLike.coe_subset_coe]
  refine fun p => ⟨?_, fun h_I_p => ?_⟩
  · rintro ⟨p, hp, rfl⟩ a ha
    exact hp ha
  · have hp : ker f ≤ p.asIdeal := (Ideal.comap_mono bot_le).trans h_I_p
    refine ⟨⟨p.asIdeal.map f, Ideal.map_isPrime_of_surjective hf hp⟩, fun x hx => ?_, ?_⟩
    · obtain ⟨x', rfl⟩ := hf x
      exact Ideal.mem_map_of_mem f (h_I_p hx)
    · ext x
      rw [comap_asIdeal, Ideal.mem_comap, Ideal.mem_map_iff_of_surjective f hf]
      refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
      rintro ⟨x', hx', heq⟩
      rw [← sub_sub_cancel x' x]
      refine p.asIdeal.sub_mem hx' (hp ?_)
      rwa [mem_ker, map_sub, sub_eq_zero]
/-
**range_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_comap_of_surjective (hf : Surjective f) : Set.range (comap f) = zero
Locus (ker f)
参数：hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `PrimeSpectrum.zeroLocus_bot`：zeroLocus_bot : zeroLocus ((⊥ : Ideal R) : 
Set R) = Set.univ
· 使用定理 `image_comap_zeroLocus_eq_zeroLocus_comap`：image_comap_zeroLocus_eq_zeroL
ocus_comap (hf : Surjective f) (I : Ideal S) : comap f '' zeroLocus I = zeroLocu
s (I.comap f)
-/
theorem range_comap_of_surjective (hf : Surjective f) :
    Set.range (comap f) = zeroLocus (ker f) := by
  rw [← Set.image_univ]
  convert! image_comap_zeroLocus_eq_zeroLocus_comap _ _ hf _
  rw [zeroLocus_bot]

variable {S}

set_option backward.isDefEq.respectTransparency false in
/-- Let `f : R →+* S` be a surjective ring homomorphism, then `Spec S` is order-isomorphic to `Z(I)`
  where `I = ker f`. -/
/-
**Ideal.primeSpectrumOrderIsoZeroLocusOfSurj** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (hf : Surjective f) {I : Ideal 
R} (hI : RingHom.ker f = I) : PrimeSpectrum S ≃o (PrimeSpectrum.zeroLocus (R
参数：hf : Surjective f；hI : RingHom.ker f = I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : R →+* S` be a surjective ring homomorphism, then `Spec S` is order-isom
orphic to `Z(I)`
  where `I = ker f`.
-/
noncomputable def Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (hf : Surjective f) {I : Ideal R}
    (hI : RingHom.ker f = I) : PrimeSpectrum S ≃o (PrimeSpectrum.zeroLocus (R := R) I) where
  toFun p := ⟨p.comap f, hI.symm.trans_le (Ideal.ker_le_comap f)⟩
  invFun := fun ⟨⟨p, _⟩, hp⟩ ↦ ⟨p.map f, p.map_isPrime_of_surjective hf (hI.trans_le hp)⟩
  left_inv := by
    intro ⟨p, _⟩
    simp only [PrimeSpectrum.mk.injEq]
    exact p.map_comap_of_surjective f hf
  right_inv := by
    intro ⟨⟨p, _⟩, hp⟩
    simp only [Subtype.mk.injEq, PrimeSpectrum.ext_iff, comap_asIdeal]
    exact (p.comap_map_of_surjective f hf).trans <| sup_eq_left.mpr (hI.trans_le hp)
  map_rel_iff' {a b} := by
    change a.asIdeal.comap _ ≤ b.asIdeal.comap _ ↔ a ≤ b
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_comap_of_surjective f hf,
      PrimeSpectrum.asIdeal_le_asIdeal]

/-- `Spec (R / I)` is order-isomorphic to `Z(I)`. -/
/-
**Ideal.primeSpectrumQuotientOrderIsoZeroLocus** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.primeSpectrumQuotientOrderIsoZeroLocus (I : Ideal R) : PrimeSpectrum
 (R ⧸ I) ≃o (PrimeSpectrum.zeroLocus (R
参数：I : Ideal R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
`Spec (R / I)` is order-isomorphic to `Z(I)`.
-/
noncomputable def Ideal.primeSpectrumQuotientOrderIsoZeroLocus (I : Ideal R) :
    PrimeSpectrum (R ⧸ I) ≃o (PrimeSpectrum.zeroLocus (R := R) I) :=
  primeSpectrumOrderIsoZeroLocusOfSurj (Quotient.mk I) Quotient.mk_surjective I.mk_ker

/-- `p` is in the image of `Spec S → Spec R` if and only if `p` extended to `S` and
restricted back to `R` is `p`. -/
/-
**PrimeSpectrum.mem_range_comap_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrimeSpectrum.mem_range_comap_iff {p : PrimeSpectrum R} : p in Set.range (
comap f) ↔ (p.asIdeal.map f).comap f = p.asIdeal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_map_comap`：comap_map_comap : ((K.comap f).map f).comap f = K
.comap f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Ideal.comap_map_eq_self_iff_of_isPrime`：comap_map_eq_self_iff_of_isPrime
 {S : Type*} [CommSemiring S] {f : R ->+* S} (p : Ideal R) [p.IsPrime] : (p.map 
f).comap f = p ↔ (exists (q …
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y

--- 原说明 ---
`p` is in the image of `Spec S → Spec R` if and only if `p` extended to `S` and
restricted back to `R` is `p`.
-/
lemma PrimeSpectrum.mem_range_comap_iff {p : PrimeSpectrum R} :
    p ∈ Set.range (comap f) ↔ (p.asIdeal.map f).comap f = p.asIdeal := by
  refine ⟨fun ⟨q, hq⟩ ↦ by simp [← hq], ?_⟩
  rw [Ideal.comap_map_eq_self_iff_of_isPrime]
  rintro ⟨q, _, hq⟩
  exact ⟨⟨q, inferInstance⟩, PrimeSpectrum.ext hq⟩

open TensorProduct

/-- A prime `p` is in the range of `Spec S → Spec R` if the fiber over `p` is nontrivial. -/
/-
**PrimeSpectrum.nontrivial_iff_mem_rangeComap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrimeSpectrum.nontrivial_iff_mem_rangeComap {S : Type*} [CommRing S] [Alge
bra R S] (p : PrimeSpectrum R) : Nontrivial (p.asIdeal.ResidueField otimes[R] S)
 ↔ p in Set.range (comap (algebraMap R S))
参数：p : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.exists_maximal`：exists_maximal [Nontrivial α] : exists M : Ideal α
, M.IsMaximal
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.comap_comp_apply`：comap_comp_apply (f : R ->+* S) (g : S -
>+* S') (x : PrimeSpectrum S') : comap (g.comp f) x = comap f (comap g x)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap`：includeLeftRin
gHom_comp_algebraMap : (includeLeftRingHom.comp (algebraMap R A) : R ->+* A otim
es[R] B) = includeRight.toRingHom.comp (algebr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `Ideal.eq_bot_of_prime`：eq_bot_of_prime [h : I.IsPrime] : I = ⊥
· 使用引理 `Ideal.ker_algebraMap_residueField`：Ideal.ker_algebraMap_residueField : R
ingHom.ker (algebraMap R I.ResidueField) = I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
A prime `p` is in the range of `Spec S → Spec R` if the fiber over `p` is nontri
vial.
-/
lemma PrimeSpectrum.nontrivial_iff_mem_rangeComap {S : Type*} [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) :
    Nontrivial (p.asIdeal.ResidueField ⊗[R] S) ↔ p ∈ Set.range (comap (algebraMap R S)) := by
  let k := p.asIdeal.ResidueField
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
    use PrimeSpectrum.comap (Algebra.TensorProduct.includeRight).toRingHom ⟨m, hm.isPrime⟩
    ext : 1
    rw [← PrimeSpectrum.comap_comp_apply,
      ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, comap_comp_apply]
    simp [Ideal.eq_bot_of_prime, k, ← RingHom.ker_eq_comap_bot]
  · obtain ⟨q, rfl⟩ := h
    let f : k ⊗[R] S →ₐ[R] q.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift (Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) rfl)
        (IsScalarTower.toAlgHom _ _ _) (fun _ _ ↦ Commute.all ..)
    exact RingHom.domain_nontrivial f.toRingHom
/-
**RingHom.strictMono_comap_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.strictMono_comap_of_surjective {S : Type*} [CommRing S] {f : R ->+
* S} (hf : Function.Surjective f) : StrictMono (comap f)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
-/
lemma RingHom.strictMono_comap_of_surjective {S : Type*} [CommRing S]
    {f : R →+* S} (hf : Function.Surjective f) : StrictMono (comap f) :=
  fun _ _ h ↦ (Ideal.relIsoOfSurjective _ hf).strictMono h

end SpecOfSurjective

section ResidueField

variable {R : Type*} [CommRing R]

/-
**PrimeSpectrum.residueField_comap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrimeSpectrum.residueField_comap (I : PrimeSpectrum R) : Set.range (comap 
(algebraMap R I.asIdeal.ResidueField)) = {I}
参数：I : PrimeSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_unique`：range_unique [Unique ι] : range f = {f default}
· 使用定理 `Set.singleton_eq_singleton_iff`：singleton_eq_singleton_iff {x y : α} : {
x} = ({y} : Set α) ↔ x = y
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用引理 `Ideal.algebraMap_residueField_eq_zero`：Ideal.algebraMap_residueField_eq_
zero {x} : algebraMap R I.ResidueField x = 0 ↔ x in I
-/
lemma PrimeSpectrum.residueField_comap (I : PrimeSpectrum R) :
    Set.range (comap (algebraMap R I.asIdeal.ResidueField)) = {I} := by
  rw [Set.range_unique, Set.singleton_eq_singleton_iff]
  exact PrimeSpectrum.ext (Ideal.ext fun x ↦ Ideal.algebraMap_residueField_eq_zero)

end ResidueField

variable {R S} in
/-
**IsLocalHom.of_comap_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalHom.of_comap_surjective [CommSemiring R] [CommSemiring S] (f : R ->
+* S) (hf : Function.Surjective (comap f)) : IsLocalHom f where map_nonunit x hf
x
参数：f : R ->+* S；hf : Function.Surjective (comap f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `exists_max_ideal_of_mem_nonunits`：exists_max_ideal_of_mem_nonunits [Comm
Semiring α] (h : a in nonunits α) : exists I : Ideal α, I.IsMaximal ∧ a in I
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem IsLocalHom.of_comap_surjective [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (hf : Function.Surjective (comap f)) : IsLocalHom f where
  map_nonunit x hfx := by
    by_contra hx
    obtain ⟨p, hp, _⟩ := exists_max_ideal_of_mem_nonunits hx
    obtain ⟨⟨q, hqp⟩, hq⟩ := hf ⟨p, hp.isPrime⟩
    simp only [PrimeSpectrum.ext_iff, comap_asIdeal] at hq
    exact hqp.ne_top (q.eq_top_of_isUnit_mem (q.mem_comap.mp (by rwa [hq])) hfx)
