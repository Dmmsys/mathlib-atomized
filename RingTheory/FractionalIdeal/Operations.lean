/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.Field

/-!
# More operations on fractional ideals

## Main definitions
* `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R⁰ = R \ {0}` (i.e. the field of fractions).
* `FractionalIdeal R⁰ K` is the type of fractional ideals in the field of fractions
* `Div (FractionalIdeal R⁰ K)` instance:
  the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statement

  * `isNoetherian` states that every fractional ideal of a Noetherian integral domain is Noetherian

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

@[expose] public section


open IsLocalization Pointwise nonZeroDivisors

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]
variable [Algebra R P]

section

variable {P' : Type*} [CommRing P'] [Algebra R P']
variable {P'' : Type*} [CommRing P''] [Algebra R P'']

/-
**FractionalIdeal._root_.IsFractional.map** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsFractional.map (g : P →ₐ[R] P') {I : Submodule R P} :
    IsFractional S I → IsFractional S (Submodule.map g.toLinearMap I)
  | ⟨a, a_nonzero, hI⟩ =>
    ⟨a, a_nonzero, fun b hb => by
      obtain ⟨b', b'_mem, hb'⟩ := Submodule.mem_map.mp hb
      rw [AlgHom.toLinearMap_apply] at hb'
      obtain ⟨x, hx⟩ := hI b' b'_mem
      use x
      rw [← g.commutes, hx, map_smul, hb']⟩

/-- `I.map g` is the pushforward of the fractional ideal `I` along the algebra morphism `g` -/
/-
**FractionalIdeal.map** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：map (g : P ->ₐ[R] P') : FractionalIdeal S P -> FractionalIdeal S P'
参数：g : P ->ₐ[R] P'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`I.map g` is the pushforward of the fractional ideal `I` along the algebra morph
ism `g`
-/
def map (g : P →ₐ[R] P') : FractionalIdeal S P → FractionalIdeal S P' := fun I =>
  ⟨Submodule.map g.toLinearMap I, I.isFractional.map g⟩

@[simp, norm_cast]
/-
**FractionalIdeal.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_map (g : P ->ₐ[R] P') (I : FractionalIdeal S P) : ↑(map g I) = Submodu
le.map g.toLinearMap I
参数：g : P ->ₐ[R] P'；I : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (g : P →ₐ[R] P') (I : FractionalIdeal S P) :
    ↑(map g I) = Submodule.map g.toLinearMap I :=
  rfl

@[simp]
/-
**FractionalIdeal.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_map {I : FractionalIdeal S P} {g : P ->ₐ[R] P'} {y : P'} : y in I.map 
g ↔ exists x, x in I ∧ g x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
-/
theorem mem_map {I : FractionalIdeal S P} {g : P →ₐ[R] P'} {y : P'} :
    y ∈ I.map g ↔ ∃ x, x ∈ I ∧ g x = y :=
  Submodule.mem_map

variable (I J : FractionalIdeal S P) (g : P →ₐ[R] P')

@[simp]
/-
**FractionalIdeal.map_id** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：map_id : I.map (AlgHom.id _ _) = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
-/
theorem map_id : I.map (AlgHom.id _ _) = I :=
  coeToSubmodule_injective (Submodule.map_id (I : Submodule R P))

@[simp]
/-
**FractionalIdeal.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：map_comp (g' : P' ->ₐ[R] P'') : I.map (g'.comp g) = (I.map g).map g'
参数：g' : P' ->ₐ[R] P''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
-/
theorem map_comp (g' : P' →ₐ[R] P'') : I.map (g'.comp g) = (I.map g).map g' :=
  coeToSubmodule_injective (Submodule.map_comp g.toLinearMap g'.toLinearMap I)

@[simp, norm_cast]
/-
**FractionalIdeal.map_coeIdeal** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：map_coeIdeal (I : Ideal R) : (I : FractionalIdeal S P).map g = I
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_coeIdeal (I : Ideal R) : (I : FractionalIdeal S P).map g = I := by
  ext x
  simp

@[simp]
/-
**FractionalIdeal.map_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R} {P : Type u_2} [ins
t_1 : CommRing P] [inst_2 : Algebra R P]   {P' : Type u_3} [inst_3 : CommRing P'
] [inst_4 : Algebra R P'] (g : P →ₐ[R] P'), FractionalIdeal.map g 1 = 1
参数：g : P →ₐ[R] P'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.map_coeIdeal`：map_coeIdeal (I : Ideal R) : (I : Fraction
alIdeal S P).map g = I
-/
protected theorem map_one : (1 : FractionalIdeal S P).map g = 1 :=
  map_coeIdeal g ⊤

@[simp]
/-
**FractionalIdeal.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R} {P : Type u_2} [ins
t_1 : CommRing P] [inst_2 : Algebra R P]   {P' : Type u_3} [inst_3 : CommRing P'
] [inst_4 : Algebra R P'] (g : P →ₐ[R] P'), FractionalIdeal.map g 0 = 0
参数：g : P →ₐ[R] P'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.map_coeIdeal`：map_coeIdeal (I : Ideal R) : (I : Fraction
alIdeal S P).map g = I
-/
protected theorem map_zero : (0 : FractionalIdeal S P).map g = 0 :=
  map_coeIdeal g 0

@[simp]
/-
**FractionalIdeal.map_add** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R} {P : Type u_2} [ins
t_1 : CommRing P] [inst_2 : Algebra R P]   {P' : Type u_3} [inst_3 : CommRing P'
] [inst_4 : Algebra R P'] (I J : FractionalIdeal S P) (g : P →ₐ[R] P'),   Fracti
onalIdeal.map g (I + J) = FractionalIdeal.map g I + FractionalIdeal.map g J
参数：I J : FractionalIdeal S P；g : P →ₐ[R] P'；I + J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
-/
protected theorem map_add : (I + J).map g = I.map g + J.map g :=
  coeToSubmodule_injective (Submodule.map_sup _ _ _)

@[simp]
/-
**FractionalIdeal.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R} {P : Type u_2} [ins
t_1 : CommRing P] [inst_2 : Algebra R P]   {P' : Type u_3} [inst_3 : CommRing P'
] [inst_4 : Algebra R P'] (I J : FractionalIdeal S P) (g : P →ₐ[R] P'),   Fracti
onalIdeal.map g (I * J) = FractionalIdeal.map g I * FractionalIdeal.map g J
参数：I J : FractionalIdeal S P；g : P →ₐ[R] P'；I * J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractional.mul`：∀ {R : Type u_1} [inst : CommRing R] {S : Submonoid R}
 {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {I J : Submodule 
R P}, …
· 使用定理 `FractionalIdeal.isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : 
FractionalIdeal S …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.mul_def`：mul_def (I J : FractionalIdeal S P) : I * J = ⟨
I * J, I.isFractional.mul J.isFractional⟩
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `Submodule.map_mul`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : Semiring A] [inst_2 : Algebra R A] (M N : Submodule R A)   {A' : Type u
_1} [in…
-/
protected theorem map_mul : (I * J).map g = I.map g * J.map g := by
  simp only [mul_def]
  exact coeToSubmodule_injective (Submodule.map_mul _ _ _)

@[simp]
/-
**FractionalIdeal.map_map_symm** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：map_map_symm (g : P ≃ₐ[R] P') : (I.map (g : P ->ₐ[R] P')).map (g.symm : P'
 ->ₐ[R] P) = I
参数：g : P ≃ₐ[R] P'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.map_comp`：map_comp (g' : P' ->ₐ[R] P'') : I.map (g'.comp
 g) = (I.map g).map g'
· 使用定理 `AlgEquiv.symm_comp`：symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e
 : A₁ ->ₐ[R] A₂) = AlgHom.id R A₁
· 使用定理 `FractionalIdeal.map_id`：map_id : I.map (AlgHom.id _ _) = I
-/
theorem map_map_symm (g : P ≃ₐ[R] P') : (I.map (g : P →ₐ[R] P')).map (g.symm : P' →ₐ[R] P) = I := by
  rw [← map_comp, g.symm_comp, map_id]

@[simp]
/-
**FractionalIdeal.map_symm_map** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：map_symm_map (I : FractionalIdeal S P') (g : P ≃ₐ[R] P') : (I.map (g.symm 
: P' ->ₐ[R] P)).map (g : P ->ₐ[R] P') = I
参数：I : FractionalIdeal S P'；g : P ≃ₐ[R] P'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.map_comp`：map_comp (g' : P' ->ₐ[R] P'') : I.map (g'.comp
 g) = (I.map g).map g'
· 使用定理 `AlgEquiv.comp_symm`：comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ ->
ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂
· 使用定理 `FractionalIdeal.map_id`：map_id : I.map (AlgHom.id _ _) = I
-/
theorem map_symm_map (I : FractionalIdeal S P') (g : P ≃ₐ[R] P') :
    (I.map (g.symm : P' →ₐ[R] P)).map (g : P →ₐ[R] P') = I := by
  rw [← map_comp, g.comp_symm, map_id]
/-
**FractionalIdeal.map_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：map_mem_map {f : P ->ₐ[R] P'} (h : Function.Injective f) {x : P} {I : Frac
tionalIdeal S P} : f x in map f I ↔ x in I
参数：h : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FractionalIdeal.mem_map`：mem_map {I : FractionalIdeal S P} {g : P ->ₐ[R]
 P'} {y : P'} : y in I.map g ↔ exists x, x in I ∧ g x = y
-/
theorem map_mem_map {f : P →ₐ[R] P'} (h : Function.Injective f) {x : P} {I : FractionalIdeal S P} :
    f x ∈ map f I ↔ x ∈ I :=
  mem_map.trans ⟨fun ⟨_, hx', x'_eq⟩ => h x'_eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩
/-
**FractionalIdeal.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：map_injective (f : P ->ₐ[R] P') (h : Function.Injective f) : Function.Inje
ctive (map f : FractionalIdeal S P -> FractionalIdeal S P')
参数：f : P ->ₐ[R] P'；h : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FractionalIdeal.map_mem_map`：map_mem_map {f : P ->ₐ[R] P'} (h : Function
.Injective f) {x : P} {I : FractionalIdeal S P} : f x in map f I ↔ x in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_injective (f : P →ₐ[R] P') (h : Function.Injective f) :
    Function.Injective (map f : FractionalIdeal S P → FractionalIdeal S P') := fun _ _ hIJ =>
  ext fun _ => (map_mem_map h).symm.trans (hIJ.symm ▸ map_mem_map h)

/-- If `g` is an equivalence, `map g` is an isomorphism -/
/-
**FractionalIdeal.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：mapEquiv (g : P ≃ₐ[R] P') : FractionalIdeal S P ≃+* FractionalIdeal S P' w
here toFun
参数：g : P ≃ₐ[R] P'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is an equivalence, `map g` is an isomorphism
-/
def mapEquiv (g : P ≃ₐ[R] P') : FractionalIdeal S P ≃+* FractionalIdeal S P' where
  toFun := map g
  invFun := map g.symm
  map_add' I J := FractionalIdeal.map_add I J _
  map_mul' I J := FractionalIdeal.map_mul I J _
  left_inv I := by rw [← map_comp, AlgEquiv.symm_comp, map_id]
  right_inv I := by rw [← map_comp, AlgEquiv.comp_symm, map_id]

@[simp]
/-
**FractionalIdeal.coeFun_mapEquiv** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeFun_mapEquiv (g : P ≃ₐ[R] P') : (mapEquiv g : FractionalIdeal S P -> Fr
actionalIdeal S P') = map g
参数：g : P ≃ₐ[R] P'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFun_mapEquiv (g : P ≃ₐ[R] P') :
    (mapEquiv g : FractionalIdeal S P → FractionalIdeal S P') = map g :=
  rfl

@[simp]
/-
**FractionalIdeal.mapEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mapEquiv_apply (g : P ≃ₐ[R] P') (I : FractionalIdeal S P) : mapEquiv g I =
 map (↑g) I
参数：g : P ≃ₐ[R] P'；I : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapEquiv_apply (g : P ≃ₐ[R] P') (I : FractionalIdeal S P) : mapEquiv g I = map (↑g) I :=
  rfl

@[simp]
/-
**FractionalIdeal.mapEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mapEquiv_symm (g : P ≃ₐ[R] P') : ((mapEquiv g).symm : FractionalIdeal S P'
 ≃+* _) = mapEquiv g.symm
参数：g : P ≃ₐ[R] P'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapEquiv_symm (g : P ≃ₐ[R] P') :
    ((mapEquiv g).symm : FractionalIdeal S P' ≃+* _) = mapEquiv g.symm :=
  rfl

@[simp]
/-
**FractionalIdeal.mapEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mapEquiv_refl : mapEquiv AlgEquiv.refl = RingEquiv.refl (FractionalIdeal S
 P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.map_id`：map_id : I.map (AlgHom.id _ _) = I
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapEquiv_refl : mapEquiv AlgEquiv.refl = RingEquiv.refl (FractionalIdeal S P) :=
  RingEquiv.ext fun x => by simp
/-
**FractionalIdeal.isFractional_span_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：isFractional_span_iff {s : Set P} : IsFractional S (span R s) ↔ exists a i
n S, forall b : P, b in s -> IsInteger R (a • b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `IsLocalization.isInteger_zero`：isInteger_zero : IsInteger R (0 : S)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `IsLocalization.isInteger_add`：isInteger_add {a b : S} (ha : IsInteger R 
a) (hb : IsInteger R b) : IsInteger R (a + b)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsLocalization.isInteger_smul`：isInteger_smul {a : R} {b : S} (hb : IsIn
teger R b) : IsInteger R (a • b)
-/
theorem isFractional_span_iff {s : Set P} :
    IsFractional S (span R s) ↔ ∃ a ∈ S, ∀ b : P, b ∈ s → IsInteger R (a • b) :=
  ⟨fun ⟨a, a_mem, h⟩ => ⟨a, a_mem, fun b hb => h b (subset_span hb)⟩, fun ⟨a, a_mem, h⟩ =>
    ⟨a, a_mem, fun _ hb =>
      span_induction (hx := hb) h
        (by
          rw [smul_zero]
          exact isInteger_zero)
        (fun x y _ _ hx hy => by
          rw [smul_add]
          exact isInteger_add hx hy)
        fun s x _ hx => by
        rw [smul_comm]
        exact isInteger_smul hx⟩⟩
/-
**FractionalIdeal.isFractional_of_fg** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：isFractional_of_fg [IsLocalization S P] {I : Submodule R P} (hI : I.FG) : 
IsFractional S I
参数：hI : I.FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.exist_integer_multiples_of_finset`：exist_integer_multiple
s_of_finset (s : Finset S) : exists b : M, forall a in s, IsInteger R ((b : R) •
 a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.isFractional_span_iff`：isFractional_span_iff {s : Set P}
 : IsFractional S (span R s) ↔ exists a in S, forall b : P, b in s -> IsInteger 
R (a • b)
-/
theorem isFractional_of_fg [IsLocalization S P] {I : Submodule R P} (hI : I.FG) :
    IsFractional S I := by
  rcases hI with ⟨I, rfl⟩
  rcases exist_integer_multiples_of_finset S I with ⟨⟨s, hs1⟩, hs⟩
  rw [isFractional_span_iff]
  exact ⟨s, hs1, hs⟩
/-
**FractionalIdeal.mem_span_mul_finite_of_mem_mul** 是 Mathlib 中的一个定理，位于命名空间 `Frac
tionalIdeal`。
形式化陈述：mem_span_mul_finite_of_mem_mul {I J : FractionalIdeal S P} {x : P} (hx : x
 in I * J) : exists T T' : Finset P, (T : Set P) subseteq I ∧ (T' : Set P) subse
teq J ∧ x in span R (T * T' : Set P)
参数：hx : x in I * J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_span_mul_finite_of_mem_mul`：mem_span_mul_finite_of_mem_mul
 {P Q : Submodule R A} {x : A} (hx : x in P * Q) : exists T T' : Finset A, (T : 
Set A) subseteq P ∧ (T' : Set …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mem_coe`：mem_coe {I : FractionalIdeal S P} {x : P} : x i
n (I : Submodule R P) ↔ x in I
-/
theorem mem_span_mul_finite_of_mem_mul {I J : FractionalIdeal S P} {x : P} (hx : x ∈ I * J) :
    ∃ T T' : Finset P, (T : Set P) ⊆ I ∧ (T' : Set P) ⊆ J ∧ x ∈ span R (T * T' : Set P) :=
  Submodule.mem_span_mul_finite_of_mem_mul (by simpa using mem_coe.mpr hx)
/-
**FractionalIdeal._root_.Units.submodule_isFractional** 是 Mathlib 中的一个引理，位于命名空间 
`FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Units.submodule_isFractional [IsLocalization S P] (I : (Submodule R P)ˣ) :
    IsFractional S I.1 :=
  FractionalIdeal.isFractional_of_fg (fg_unit _)

set_option backward.isDefEq.respectTransparency false in
/-- If P is a localization of R, invertible R-submodules of P are all fractional
(expressed as an isomorphism of groups). -/
/-
**FractionalIdeal.unitsMulEquivSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `FractionalId
eal`。
形式化陈述：unitsMulEquivSubmodule [IsLocalization S P] : (FractionalIdeal S P)ˣ ≃* (S
ubmodule R P)ˣ where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Units.submodule_isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   [IsLo
calization S P] (I…

--- 原说明 ---
If P is a localization of R, invertible R-submodules of P are all fractional
(expressed as an isomorphism of groups).
-/
def unitsMulEquivSubmodule [IsLocalization S P] :
    (FractionalIdeal S P)ˣ ≃* (Submodule R P)ˣ where
  __ := Units.map (coeSubmoduleHom S P)
  invFun I := ⟨⟨I, I.submodule_isFractional⟩, ⟨↑I⁻¹, I⁻¹.submodule_isFractional⟩,
    coeToSubmodule_inj.mp <| by rw [coe_mul, coe_one]; exact I.mul_inv,
    coeToSubmodule_inj.mp <| by rw [coe_mul, coe_one]; exact I.inv_mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (S) in
/-
**FractionalIdeal.coeIdeal_fg** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_fg (inj : Function.Injective (algebraMap R P)) (I : Ideal R) : FG
 ((I : FractionalIdeal S P) : Submodule R P) ↔ I.FG
参数：inj : Function.Injective (algebraMap R P)；I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.coeSubmodule_fg`：coeSubmodule_fg (hS : Function.Injective
 (algebraMap R S)) (I : Ideal R) : Submodule.FG (coeSubmodule S I) ↔ Submodule.F
G I
-/
theorem coeIdeal_fg (inj : Function.Injective (algebraMap R P)) (I : Ideal R) :
    FG ((I : FractionalIdeal S P) : Submodule R P) ↔ I.FG :=
  coeSubmodule_fg _ inj _
/-
**FractionalIdeal.fg_unit** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：fg_unit (I : (FractionalIdeal S P)ˣ) : FG (I : Submodule R P)
参数：I : (FractionalIdeal S P)ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_unit`：fg_unit {R A : Type*} [CommSemiring R] [Semiring A] [
Algebra R A] (I : (Submodule R A)ˣ) : (I : Submodule R A).FG
-/
theorem fg_unit (I : (FractionalIdeal S P)ˣ) : FG (I : Submodule R P) :=
  Submodule.fg_unit <| Units.map (coeSubmoduleHom S P).toMonoidHom I
/-
**FractionalIdeal.fg_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：fg_of_isUnit (I : FractionalIdeal S P) (h : IsUnit I) : FG (I : Submodule 
R P)
参数：I : FractionalIdeal S P；h : IsUnit I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.fg_unit`：fg_unit (I : (FractionalIdeal S P)ˣ) : FG (I : 
Submodule R P)
-/
theorem fg_of_isUnit (I : FractionalIdeal S P) (h : IsUnit I) : FG (I : Submodule R P) :=
  fg_unit h.unit
/-
**FractionalIdeal._root_.Ideal.fg_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Fractiona
lIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ideal.fg_of_isUnit (inj : Function.Injective (algebraMap R P)) (I : Ideal R)
    (h : IsUnit (I : FractionalIdeal S P)) : I.FG := by
  rw [← coeIdeal_fg S inj I]
  exact FractionalIdeal.fg_of_isUnit (R := R) I h

variable (S P P')

variable [IsLocalization S P] [IsLocalization S P']

/-- `canonicalEquiv f f'` is the canonical equivalence between the fractional
ideals in `P` and in `P'`, which are both localizations of `R` at `S`. -/
noncomputable irreducible_def canonicalEquiv : FractionalIdeal S P ≃+* FractionalIdeal S P' :=
  mapEquiv
    { ringEquivOfRingEquiv P P' (RingEquiv.refl R)
        (show S.map _ = S by rw [RingEquiv.toMonoidHom_refl, Submonoid.map_id]) with
      commutes' := fun _ => ringEquivOfRingEquiv_eq _ _ }

@[simp]
/-
**FractionalIdeal.mem_canonicalEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fractional
Ideal`。
形式化陈述：mem_canonicalEquiv_apply {I : FractionalIdeal S P} {x : P'} : x in canonic
alEquiv S P P' I ↔ exists y in I, IsLocalization.map P' (RingHom.id R) (fun y (h
y : y in S) => show RingHom.id R y in S from hy) (y : P) = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.canonicalEquiv_def`：∀ {R : Type u_5} [inst : CommRing R]
 (S : Submonoid R) (P : Type u_6) [inst_1 : CommRing P] [inst_2 : Algebra R P]  
 (P' : Type u_7) [inst_3…
· 使用定理 `FractionalIdeal.mapEquiv_apply`：mapEquiv_apply (g : P ≃ₐ[R] P') (I : Fra
ctionalIdeal S P) : mapEquiv g I = map (↑g) I
· 使用定理 `FractionalIdeal.mem_map`：mem_map {I : FractionalIdeal S P} {g : P ->ₐ[R]
 P'} {y : P'} : y in I.map g ↔ exists x, x in I ∧ g x = y
-/
theorem mem_canonicalEquiv_apply {I : FractionalIdeal S P} {x : P'} :
    x ∈ canonicalEquiv S P P' I ↔
      ∃ y ∈ I,
        IsLocalization.map P' (RingHom.id R) (fun y (hy : y ∈ S) => show RingHom.id R y ∈ S from hy)
            (y : P) =
          x := by
  rw [canonicalEquiv, mapEquiv_apply, mem_map]
  exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩

@[simp]
/-
**FractionalIdeal.canonicalEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal
`。
形式化陈述：canonicalEquiv_symm : (canonicalEquiv S P P').symm = canonicalEquiv S P' P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.mem_canonicalEquiv_apply`：mem_canonicalEquiv_apply {I : 
FractionalIdeal S P} {x : P'} : x in canonicalEquiv S P P' I ↔ exists y in I, Is
Localization.map P' (RingHom.i…
· 使用定理 `FractionalIdeal.canonicalEquiv_def`：∀ {R : Type u_5} [inst : CommRing R]
 (S : Submonoid R) (P : Type u_6) [inst_1 : CommRing P] [inst_2 : Algebra R P]  
 (P' : Type u_7) [inst_3…
· 使用定理 `FractionalIdeal.mapEquiv_symm`：mapEquiv_symm (g : P ≃ₐ[R] P') : ((mapEqu
iv g).symm : FractionalIdeal S P' ≃+* _) = mapEquiv g.symm
· 使用定理 `FractionalIdeal.mapEquiv_apply`：mapEquiv_apply (g : P ≃ₐ[R] P') (I : Fra
ctionalIdeal S P) : mapEquiv g I = map (↑g) I
· 使用定理 `FractionalIdeal.mem_map`：mem_map {I : FractionalIdeal S P} {g : P ->ₐ[R]
 P'} {y : P'} : y in I.map g ↔ exists x, x in I ∧ g x = y
-/
theorem canonicalEquiv_symm : (canonicalEquiv S P P').symm = canonicalEquiv S P' P :=
  RingEquiv.ext fun I =>
    SetLike.ext_iff.mpr fun x => by
      rw [mem_canonicalEquiv_apply, canonicalEquiv, mapEquiv_symm, mapEquiv_apply,
        mem_map]
      exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩
/-
**FractionalIdeal.canonicalEquiv_flip** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal
`。
形式化陈述：canonicalEquiv_flip (I) : canonicalEquiv S P P' (canonicalEquiv S P' P I) 
= I
参数：I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.canonicalEquiv_symm`：canonicalEquiv_symm : (canonicalEqu
iv S P P').symm = canonicalEquiv S P' P
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
theorem canonicalEquiv_flip (I) : canonicalEquiv S P P' (canonicalEquiv S P' P I) = I := by
  rw [← canonicalEquiv_symm, RingEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FractionalIdeal.canonicalEquiv_canonicalEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Fract
ionalIdeal`。
形式化陈述：canonicalEquiv_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra R P'']
 [IsLocalization S P''] (I : FractionalIdeal S P) : canonicalEquiv S P' P'' (can
onicalEquiv S P P' I) = canonicalEquiv S P P'' I
参数：P'' : Type*；I : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.map_map`：map_map {A : Type*} [CommSemiring A] {U : Submon
oid A} {W} [CommSemiring W] [Algebra A W] [IsLocalization U W] {l : P ->+* A} (h
l : T <= U.c…
· 使用定理 `IsLocalization.map.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M M_1 : Submonoid R} (e_M : M = M_1) {S : Type u_2} [inst_1 : CommSemiring S]  
 [inst_2 : Algebra …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem canonicalEquiv_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra R P'']
    [IsLocalization S P''] (I : FractionalIdeal S P) :
    canonicalEquiv S P' P'' (canonicalEquiv S P P' I) = canonicalEquiv S P P'' I := by
  ext
  simp [IsLocalization.map_map]
/-
**FractionalIdeal.canonicalEquiv_trans_canonicalEquiv** 是 Mathlib 中的一个定理，位于命名空间 
`FractionalIdeal`。
形式化陈述：canonicalEquiv_trans_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra 
R P''] [IsLocalization S P''] : (canonicalEquiv S P P').trans (canonicalEquiv S 
P' P'') = canonicalEquiv S P P''
参数：P'' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `FractionalIdeal.canonicalEquiv_canonicalEquiv`：canonicalEquiv_canonicalE
quiv (P'' : Type*) [CommRing P''] [Algebra R P''] [IsLocalization S P''] (I : Fr
actionalIdeal S P) : canonicalEquiv…
-/
theorem canonicalEquiv_trans_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra R P'']
    [IsLocalization S P''] :
    (canonicalEquiv S P P').trans (canonicalEquiv S P' P'') = canonicalEquiv S P P'' :=
  RingEquiv.ext (canonicalEquiv_canonicalEquiv S P P' P'')

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FractionalIdeal.canonicalEquiv_coeIdeal** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
形式化陈述：canonicalEquiv_coeIdeal (I : Ideal R) : canonicalEquiv S P P' I = I
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem canonicalEquiv_coeIdeal (I : Ideal R) : canonicalEquiv S P P' I = I := by
  ext
  simp [IsLocalization.map_eq]

@[simp]
/-
**FractionalIdeal.canonicalEquiv_self** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal
`。
形式化陈述：canonicalEquiv_self : canonicalEquiv S P P = RingEquiv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.canonicalEquiv_trans_canonicalEquiv`：canonicalEquiv_tran
s_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra R P''] [IsLocalization S 
P''] : (canonicalEquiv S P P').trans (can…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `FractionalIdeal.canonicalEquiv_symm`：canonicalEquiv_symm : (canonicalEqu
iv S P P').symm = canonicalEquiv S P' P
· 使用定理 `RingEquiv.symm_trans_self`：symm_trans_self (e : R ≃+* S) : e.symm.trans 
e = RingEquiv.refl S
-/
theorem canonicalEquiv_self : canonicalEquiv S P P = RingEquiv.refl _ := by
  rw [← canonicalEquiv_trans_canonicalEquiv S P P]
  convert! (canonicalEquiv S P P).symm_trans_self
  exact (canonicalEquiv_symm S P P).symm

end

section IsFractionRing

/-!
### `IsFractionRing` section

This section concerns fractional ideals in the field of fractions,
i.e. the type `FractionalIdeal R⁰ K` where `IsFractionRing R K`.
-/


variable {K K' : Type*} [Field K] [Field K']
variable [Algebra R K] [IsFractionRing R K] [Algebra R K'] [IsFractionRing R K']
variable {I J : FractionalIdeal R⁰ K} (h : K →ₐ[R] K')

/-- Nonzero fractional ideals contain a nonzero integer. -/
/-
**FractionalIdeal.exists_ne_zero_mem_isInteger** 是 Mathlib 中的一个定理，位于命名空间 `Fracti
onalIdeal`。
形式化陈述：exists_ne_zero_mem_isInteger [Nontrivial R] (hI : I != 0) : exists x, x !=
 0 ∧ algebraMap R K x in I
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.exists_of_lt`：exists_of_lt : p < q -> exists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.exists_integer_multiple`：exists_integer_multiple (a : S) 
: exists b : M, IsInteger R ((b : R) • a)
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsFractionRing.to_map_eq_zero_iff`：to_map_eq_zero_iff {x : R} : algebraM
ap R K x = 0 ↔ x = 0
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors`：∀ {R : Type u_1} [
inst : CommRing R] {K : Type u_5} [inst_1 : CommRing K] [inst_2 : Algebra R K] [
IsFractionRing R K]   [Nontrivial R] {x : …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p

--- 原说明 ---
Nonzero fractional ideals contain a nonzero integer.
-/
theorem exists_ne_zero_mem_isInteger [Nontrivial R] (hI : I ≠ 0) :
    ∃ x, x ≠ 0 ∧ algebraMap R K x ∈ I := by
  obtain ⟨y : K, y_mem, y_notMem⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  have y_ne_zero : y ≠ 0 := by simpa using y_notMem
  obtain ⟨z, ⟨x, hx⟩⟩ := exists_integer_multiple R⁰ y
  refine ⟨x, ?_, ?_⟩
  · rw [Ne, ← @IsFractionRing.to_map_eq_zero_iff R _ K, hx, Algebra.smul_def]
    exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2) y_ne_zero
  · rw [hx]
    exact smul_mem _ _ y_mem
/-
**FractionalIdeal.map_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：map_ne_zero [Nontrivial R] (hI : I != 0) : I.map h != 0
参数：hI : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.exists_ne_zero_mem_isInteger`：exists_ne_zero_mem_isInteg
er [Nontrivial R] (hI : I != 0) : exists x, x != 0 ∧ algebraMap R K x in I
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsFractionRing.to_map_eq_zero_iff`：to_map_eq_zero_iff {x : R} : algebraM
ap R K x = 0 ↔ x = 0
· 使用定理 `FractionalIdeal.eq_zero_iff`：eq_zero_iff {I : FractionalIdeal S P} : I =
 0 ↔ forall x in I, x = (0 : P)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mem_map`：mem_map {I : FractionalIdeal S P} {g : P ->ₐ[R]
 P'} {y : P'} : y in I.map g ↔ exists x, x in I ∧ g x = y
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
theorem map_ne_zero [Nontrivial R] (hI : I ≠ 0) : I.map h ≠ 0 := by
  obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_isInteger hI
  contrapose x_ne_zero with map_eq_zero
  refine IsFractionRing.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr ?_))
  exact ⟨algebraMap R K x, hx, h.commutes x⟩

@[simp]
/-
**FractionalIdeal.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：map_eq_zero_iff [Nontrivial R] : I.map h = 0 ↔ I = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `FractionalIdeal.map_ne_zero`：map_ne_zero [Nontrivial R] (hI : I != 0) : 
I.map h != 0
· 使用定理 `FractionalIdeal.map_zero`：∀ {R : Type u_1} [inst : CommRing R] {S : Subm
onoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {P' : Typ
e u_3} [inst_3…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_eq_zero_iff [Nontrivial R] : I.map h = 0 ↔ I = 0 :=
  ⟨not_imp_not.mp (map_ne_zero _), fun hI => hI.symm ▸ FractionalIdeal.map_zero h⟩
/-
**FractionalIdeal.coeIdeal_injective** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：coeIdeal_injective : Function.Injective (fun (I : Ideal R) => (I : Fractio
nalIdeal R⁰ K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeIdeal_injective'`：coeIdeal_injective' (h : S <= nonZe
roDivisors R) : Function.Injective (fun (I : Ideal R) => (I : FractionalIdeal S 
P))
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coeIdeal_injective : Function.Injective (fun (I : Ideal R) ↦ (I : FractionalIdeal R⁰ K)) :=
  coeIdeal_injective' le_rfl
/-
**FractionalIdeal.coeIdeal_inj** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_inj {I J : Ideal R} : (I : FractionalIdeal R⁰ K) = (J : Fractiona
lIdeal R⁰ K) ↔ I = J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeIdeal_inj'`：coeIdeal_inj' (h : S <= nonZeroDivisors R
) {I J : Ideal R} : (I : FractionalIdeal S P) = J ↔ I = J
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coeIdeal_inj {I J : Ideal R} :
    (I : FractionalIdeal R⁰ K) = (J : FractionalIdeal R⁰ K) ↔ I = J :=
  coeIdeal_inj' le_rfl

@[simp]
/-
**FractionalIdeal.coeIdeal_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_eq_zero {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeIdeal_eq_zero'`：coeIdeal_eq_zero' {I : Ideal R} (h : 
S <= nonZeroDivisors R) : (I : FractionalIdeal S P) = 0 ↔ I = (⊥ : Ideal R)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coeIdeal_eq_zero {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥ :=
  coeIdeal_eq_zero' le_rfl
/-
**FractionalIdeal.coeIdeal_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_ne_zero {I : Ideal R} : (I : FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeIdeal_ne_zero'`：coeIdeal_ne_zero' {I : Ideal R} (h : 
S <= nonZeroDivisors R) : (I : FractionalIdeal S P) != 0 ↔ I != (⊥ : Ideal R)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coeIdeal_ne_zero {I : Ideal R} : (I : FractionalIdeal R⁰ K) ≠ 0 ↔ I ≠ ⊥ :=
  coeIdeal_ne_zero' le_rfl

@[simp]
/-
**FractionalIdeal.coeIdeal_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_eq_one {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 1 ↔ I = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `FractionalIdeal.coeIdeal_inj`：coeIdeal_inj {I J : Ideal R} : (I : Fracti
onalIdeal R⁰ K) = (J : FractionalIdeal R⁰ K) ↔ I = J
-/
theorem coeIdeal_eq_one {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 1 ↔ I = 1 := by
  simpa only [Ideal.one_eq_top] using! coeIdeal_inj
/-
**FractionalIdeal.coeIdeal_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coeIdeal_ne_one {I : Ideal R} : (I : FractionalIdeal R⁰ K) != 1 ↔ I != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `FractionalIdeal.coeIdeal_eq_one`：coeIdeal_eq_one {I : Ideal R} : (I : Fr
actionalIdeal R⁰ K) = 1 ↔ I = 1
-/
theorem coeIdeal_ne_one {I : Ideal R} : (I : FractionalIdeal R⁰ K) ≠ 1 ↔ I ≠ 1 :=
  not_iff_not.mpr coeIdeal_eq_one
/-
**FractionalIdeal.num_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：num_eq_zero_iff [IsDomain R] {I : FractionalIdeal R⁰ K} : I.num = 0 ↔ I = 
0 where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.zero_of_num_eq_bot`：zero_of_num_eq_bot [IsDomain R] [Mod
ule.IsTorsionFree R P] (hS : 0 ∉ S) {I : FractionalIdeal S P} (hI : I.num = ⊥) :
 I = 0
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `zero_notMem_nonZeroDivisors`：zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰
· 使用定理 `FractionalIdeal.num_zero_eq`：num_zero_eq (h_inj : Function.Injective (al
gebraMap R P)) : num (0 : FractionalIdeal S P) = 0
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem num_eq_zero_iff [IsDomain R] {I : FractionalIdeal R⁰ K} : I.num = 0 ↔ I = 0 where
  mp h := zero_of_num_eq_bot zero_notMem_nonZeroDivisors h
  mpr h := h ▸ num_zero_eq (IsFractionRing.injective R K)

end IsFractionRing

section Quotient

/-!
### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
the localization, i.e. that the localization is a field. We satisfy this
assumption by taking `S = nonZeroDivisors R`, `R`'s localization at which
is a field because `R` is a domain.
-/

variable {R₁ : Type*} [CommRing R₁] {K : Type*} [Field K]
variable [Algebra R₁ K]

/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial (FractionalIdeal R₁⁰ K) :=
  ⟨⟨0, 1, fun h =>
      have : (1 : K) ∈ (0 : FractionalIdeal R₁⁰ K) := by
        rw [← (algebraMap R₁ K).map_one]
        simpa only [h] using coe_mem_one R₁⁰ 1
      one_ne_zero ((mem_zero_iff _).mp this)⟩⟩
/-
**FractionalIdeal.ne_zero_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：ne_zero_of_mul_eq_one (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : I !=
 0
参数：I J : FractionalIdeal R₁⁰ K；h : I * J = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zero_ne_one'`：zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ne_zero_of_mul_eq_one (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : I ≠ 0 := fun hI =>
  zero_ne_one' (FractionalIdeal R₁⁰ K)
    (by
      convert! h
      simp [hI])

variable [IsFractionRing R₁ K] [IsDomain R₁]
/-
**FractionalIdeal._root_.IsFractional.div_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `
FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsFractional.div_of_nonzero {I J : Submodule R₁ K} :
    IsFractional R₁⁰ I → IsFractional R₁⁰ J → J ≠ 0 → IsFractional R₁⁰ (I / J)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩, h => by
    obtain ⟨y, mem_J, notMem_zero⟩ :=
      SetLike.exists_of_lt (show 0 < J by simpa only using! bot_lt_iff_ne_bot.mpr h)
    obtain ⟨y', hy'⟩ := hJ y mem_J
    use aI * y'
    constructor
    · apply (nonZeroDivisors R₁).mul_mem haI (mem_nonZeroDivisors_iff_ne_zero.mpr _)
      intro y'_eq_zero
      have : algebraMap R₁ K aJ * y = 0 := by
        rw [← Algebra.smul_def, ← hy', y'_eq_zero, map_zero]
      have y_zero :=
        (mul_eq_zero.mp this).resolve_left
          (mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).1 (IsFractionRing.injective _ _) _)
            (mem_nonZeroDivisors_iff_ne_zero.mp haJ))
      apply notMem_zero
      simpa
    intro b hb
    convert! hI _ (hb _ (Submodule.smul_mem _ aJ mem_J)) using 1
    rw [← hy', mul_comm b, ← Algebra.smul_def, mul_smul]
/-
**FractionalIdeal.isFractional_div_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fractio
nalIdeal`。
形式化陈述：isFractional_div_of_ne_zero {I J : FractionalIdeal R₁⁰ K} (h : J != 0) : I
sFractional R₁⁰ (I / J : Submodule R₁ K)
参数：h : J != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractional.div_of_nonzero`：∀ {R₁ : Type u_3} [inst : CommRing R₁] {K :
 Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K] [IsFractionRing R₁ K]   [I
sDomain R₁] {I J …
· 使用定理 `FractionalIdeal.isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : 
FractionalIdeal S …
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
-/
theorem isFractional_div_of_ne_zero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    IsFractional R₁⁰ (I / J : Submodule R₁ K) :=
  I.isFractional.div_of_nonzero J.isFractional fun H =>
    h <| coeToSubmodule_injective <| H.trans coe_zero.symm

open scoped Classical in
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Div (FractionalIdeal R₁⁰ K) :=
  ⟨fun I J => if h : J = 0 then 0 else ⟨I / J, isFractional_div_of_ne_zero h⟩⟩

variable {I J : FractionalIdeal R₁⁰ K}

@[simp]
/-
**FractionalIdeal.div_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `FractionalIdeal.isFractional_div_of_ne_zero`：isFractional_div_of_ne_zero
 {I J : FractionalIdeal R₁⁰ K} (h : J != 0) : IsFractional R₁⁰ (I / J : Submodul
e R₁ K)
-/
theorem div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 = 0 :=
  dif_pos rfl
/-
**FractionalIdeal.div_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：div_of_ne_zero {I J : FractionalIdeal R₁⁰ K} (h : J != 0) : I / J = ⟨I / J
, isFractional_div_of_ne_zero h⟩
参数：h : J != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `FractionalIdeal.isFractional_div_of_ne_zero`：isFractional_div_of_ne_zero
 {I J : FractionalIdeal R₁⁰ K} (h : J != 0) : IsFractional R₁⁰ (I / J : Submodul
e R₁ K)
-/
theorem div_of_ne_zero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    I / J = ⟨I / J, isFractional_div_of_ne_zero h⟩ :=
  dif_neg h

@[simp]
/-
**FractionalIdeal.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J != 0) : (↑(I / J) : Submodul
e R₁ K) = ↑I / (↑J : Submodule R₁ K)
参数：hJ : J != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `FractionalIdeal.isFractional_div_of_ne_zero`：isFractional_div_of_ne_zero
 {I J : FractionalIdeal R₁⁰ K} (h : J != 0) : IsFractional R₁⁰ (I / J : Submodul
e R₁ K)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J ≠ 0) :
    (↑(I / J) : Submodule R₁ K) = ↑I / (↑J : Submodule R₁ K) :=
  congr_arg _ (dif_neg hJ)
/-
**FractionalIdeal.mem_div_iff_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalId
eal`。
形式化陈述：mem_div_iff_of_ne_zero {I J : FractionalIdeal R₁⁰ K} (h : J != 0) {x} : x 
in I / J ↔ forall y in J, x * y in I
参数：h : J != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional_div_of_ne_zero`：isFractional_div_of_ne_zero
 {I J : FractionalIdeal R₁⁰ K} (h : J != 0) : IsFractional R₁⁰ (I / J : Submodul
e R₁ K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.div_of_ne_zero`：div_of_ne_zero {I J : FractionalIdeal R₁
⁰ K} (h : J != 0) : I / J = ⟨I / J, isFractional_div_of_ne_zero h⟩
· 使用定理 `Submodule.mem_div_iff_forall_mul_mem`：mem_div_iff_forall_mul_mem {x : A}
 {I J : Submodule R A} : x in I / J ↔ forall y in J, x * y in I
-/
theorem mem_div_iff_of_ne_zero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) {x} :
    x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I := by
  rw [div_of_ne_zero h]
  exact Submodule.mem_div_iff_forall_mul_mem
/-
**FractionalIdeal.mul_one_div_le_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：mul_one_div_le_one {I : FractionalIdeal R₁⁰ K} : I * (1 / I) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.div_zero`：div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 =
 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `FractionalIdeal.zero_le`：zero_le (I : FractionalIdeal S P) : 0 <= I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coe_le_coe`：coe_le_coe {I J : FractionalIdeal S P} : (I 
: Submodule R P) <= (J : Submodule R P) ↔ I <= J
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `FractionalIdeal.coe_div`：coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J !
= 0) : (↑(I / J) : Submodule R₁ K) = ↑I / (↑J : Submodule R₁ K)
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用定理 `Submodule.mul_one_div_le_one`：mul_one_div_le_one {I : Submodule R A} : I
 * (1 / I) <= 1
-/
theorem mul_one_div_le_one {I : FractionalIdeal R₁⁰ K} : I * (1 / I) ≤ 1 := by
  by_cases hI : I = 0
  · rw [hI, div_zero, mul_zero]
    exact zero_le 1
  · rw [← coe_le_coe, coe_mul, coe_div hI, coe_one]
    apply Submodule.mul_one_div_le_one
/-
**FractionalIdeal.le_self_mul_one_div** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal
`。
形式化陈述：le_self_mul_one_div {I : FractionalIdeal R₁⁰ K} (hI : I <= (1 : Fractional
Ideal R₁⁰ K)) : I <= I * (1 / I)
参数：hI : I <= (1 : FractionalIdeal R₁⁰ K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.div_zero`：div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 =
 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coe_le_coe`：coe_le_coe {I J : FractionalIdeal S P} : (I 
: Submodule R P) <= (J : Submodule R P) ↔ I <= J
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `FractionalIdeal.coe_div`：coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J !
= 0) : (↑(I / J) : Submodule R₁ K) = ↑I / (↑J : Submodule R₁ K)
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用定理 `Submodule.le_self_mul_one_div`：le_self_mul_one_div {I : Submodule R A} (
hI : I <= 1) : I <= I * (1 / I)
-/
theorem le_self_mul_one_div {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) :
    I ≤ I * (1 / I) := by
  by_cases hI_nz : I = 0
  · rw [hI_nz, div_zero, mul_zero]
  · rw [← coe_le_coe, coe_mul, coe_div hI_nz, coe_one]
    rw [← coe_le_coe, coe_one] at hI
    exact Submodule.le_self_mul_one_div hI
/-
**FractionalIdeal.le_div_iff_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：le_div_iff_of_ne_zero {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' != 0) : I
 <= J / J' ↔ forall x in I, forall y in J', x * y in J
参数：hJ' : J' != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_div_iff_of_ne_zero`：mem_div_iff_of_ne_zero {I J : Fr
actionalIdeal R₁⁰ K} (h : J != 0) {x} : x in I / J ↔ forall y in J, x * y in I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem le_div_iff_of_ne_zero {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' ≠ 0) :
    I ≤ J / J' ↔ ∀ x ∈ I, ∀ y ∈ J', x * y ∈ J :=
  ⟨fun h _ hx => (mem_div_iff_of_ne_zero hJ').mp (h hx), fun h x hx =>
    (mem_div_iff_of_ne_zero hJ').mpr (h x hx)⟩
/-
**FractionalIdeal.le_div_iff_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：le_div_iff_mul_le {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' != 0) : I <= 
J / J' ↔ I * J' <= J
参数：hJ' : J' != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional_div_of_ne_zero`：isFractional_div_of_ne_zero
 {I J : FractionalIdeal R₁⁰ K} (h : J != 0) : IsFractional R₁⁰ (I / J : Submodul
e R₁ K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.div_of_ne_zero`：div_of_ne_zero {I J : FractionalIdeal R₁
⁰ K} (h : J != 0) : I / J = ⟨I / J, isFractional_div_of_ne_zero h⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coe_le_coe`：coe_le_coe {I J : FractionalIdeal S P} : (I 
: Submodule R P) <= (J : Submodule R P) ↔ I <= J
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `Submodule.le_div_iff_mul_le`：le_div_iff_mul_le {I J K : Submodule R A} :
 I <= J / K ↔ I * K <= J
-/
theorem le_div_iff_mul_le {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' ≠ 0) :
    I ≤ J / J' ↔ I * J' ≤ J := by
  rw [div_of_ne_zero hJ', ← coe_le_coe (I := I * J') (J := J), coe_mul]
  exact Submodule.le_div_iff_mul_le

@[simp]
/-
**FractionalIdeal.div_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：div_one {I : FractionalIdeal R₁⁰ K} : I / 1 = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional_div_of_ne_zero`：isFractional_div_of_ne_zero
 {I J : FractionalIdeal R₁⁰ K} (h : J != 0) : IsFractional R₁⁰ (I / J : Submodul
e R₁ K)
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.div_of_ne_zero`：div_of_ne_zero {I J : FractionalIdeal R₁
⁰ K} (h : J != 0) : I / J = ⟨I / J, isFractional_div_of_ne_zero h⟩
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_div_iff_forall_mul_mem`：mem_div_iff_forall_mul_mem {x : A}
 {I J : Submodule R A} : x in I / J ↔ forall y in J, x * y in I
· 使用定理 `FractionalIdeal.coe_mem_one`：coe_mem_one (x : R) : algebraMap R P x in (
1 : FractionalIdeal S P)
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Algebra.linearMap_apply`：linearMap_apply (r : R) : Algebra.linearMap R A
 r = algebraMap R A r
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem div_one {I : FractionalIdeal R₁⁰ K} : I / 1 = I := by
  rw [div_of_ne_zero (one_ne_zero' (FractionalIdeal R₁⁰ K))]
  ext
  constructor <;> intro h
  · simpa using mem_div_iff_forall_mul_mem.mp h 1 ((algebraMap R₁ K).map_one ▸ coe_mem_one R₁⁰ 1)
  · apply mem_div_iff_forall_mul_mem.mpr
    rintro y ⟨y', _, rfl⟩
    convert! Submodule.smul_mem _ y' h using 1
    rw [mul_comm, Algebra.linearMap_apply, ← Algebra.smul_def]
/-
**FractionalIdeal.eq_one_div_of_mul_eq_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Frac
tionalIdeal`。
形式化陈述：eq_one_div_of_mul_eq_one_right (I J : FractionalIdeal R₁⁰ K) (h : I * J = 
1) : J = 1 / I
参数：I J : FractionalIdeal R₁⁰ K；h : I * J = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.ne_zero_of_mul_eq_one`：ne_zero_of_mul_eq_one (I J : Frac
tionalIdeal R₁⁰ K) (h : I * J = 1) : I != 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mul_le`：mul_le {I J K : FractionalIdeal S P} : I * J <= 
K ↔ forall i in I, forall j in J, i * j in K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_div_iff_of_ne_zero`：mem_div_iff_of_ne_zero {I J : Fr
actionalIdeal R₁⁰ K} (h : J != 0) {x} : x in I / J ↔ forall y in J, x * y in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `FractionalIdeal.instMulLeftMono`：∀ {R : Type u_1} [inst : CommRing R] {S
 : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P],   M
ulLeftMono (Fractiona…
· 使用定理 `FractionalIdeal.instMulRightMono`：∀ {R : Type u_1} [inst : CommRing R] {
S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P],   
MulRightMono (Fraction…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `FractionalIdeal.le_div_iff_of_ne_zero`：le_div_iff_of_ne_zero {I J J' : F
ractionalIdeal R₁⁰ K} (hJ' : J' != 0) : I <= J / J' ↔ forall x in I, forall y in
 J', x * y in J
· 使用定理 `FractionalIdeal.mul_mem_mul`：mul_mem_mul {I J : FractionalIdeal S P} {i 
j : P} (hi : i in I) (hj : j in J) : i * j in I * J
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
-/
theorem eq_one_div_of_mul_eq_one_right (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) :
    J = 1 / I := by
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h
  suffices h' : I * (1 / I) = 1 from
    congr_arg Units.inv <| @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
  apply le_antisymm
  · apply mul_le.mpr _
    intro x hx y hy
    rw [mul_comm]
    exact (mem_div_iff_of_ne_zero hI).mp hy x hx
  rw [← h]
  gcongr
  apply (le_div_iff_of_ne_zero hI).mpr _
  intro y hy x hx
  rw [mul_comm]
  exact mul_mem_mul hy hx
/-
**FractionalIdeal.mul_div_self_cancel_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
形式化陈述：mul_div_self_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * (1 / I) = 1 ↔ ex
ists J, I * J = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.eq_one_div_of_mul_eq_one_right`：eq_one_div_of_mul_eq_one
_right (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = 1 / I
-/
theorem mul_div_self_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * (1 / I) = 1 ↔ ∃ J, I * J = 1 :=
  ⟨fun h => ⟨1 / I, h⟩, fun ⟨J, hJ⟩ => by rwa [← eq_one_div_of_mul_eq_one_right I J hJ]⟩

variable {K' : Type*} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FractionalIdeal.map_div** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：∀ {R₁ : Type u_3} [inst : CommRing R₁] {K : Type u_4} [inst_1 : Field K] [
inst_2 : Algebra R₁ K]   [inst_3 : IsFractionRing R₁ K] [inst_4 : IsDomain R₁] {
K' : Type u_5} [inst_5 : Field K'] [inst_6 : Algebra R₁ K']   [inst_7 : IsFracti
onRing R₁ K'] (I J : FractionalIdeal (nonZeroDivisors R₁) K) (h : K ≃ₐ[R₁] K'), 
  FractionalIdeal.map (↑h) (I / J) = FractionalIdeal.map (↑h) I / FractionalIdea
l.map (↑h) J
参数：I J : FractionalIdeal (nonZeroDivisors R₁) K；h : K ≃ₐ[R₁] K'；↑h；I / J；↑h；↑h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.div_zero`：div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 =
 0
· 使用定理 `FractionalIdeal.map_zero`：∀ {R : Type u_1} [inst : CommRing R] {S : Subm
onoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {P' : Typ
e u_3} [inst_3…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FractionalIdeal.isFractional_div_of_ne_zero`：isFractional_div_of_ne_zero
 {I J : FractionalIdeal R₁⁰ K} (h : J != 0) : IsFractional R₁⁰ (I / J : Submodul
e R₁ K)
· 使用定理 `FractionalIdeal.map_ne_zero`：map_ne_zero [Nontrivial R] (hI : I != 0) : 
I.map h != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FractionalIdeal.div_of_ne_zero`：div_of_ne_zero {I J : FractionalIdeal R₁
⁰ K} (h : J != 0) : I / J = ⟨I / J, isFractional_div_of_ne_zero h⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_div`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : CommSemiring A] [inst_2 : Algebra R A] {B : Type u_1}   [inst_3 : CommS
emiring…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_div (I J : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    (I / J).map (h : K →ₐ[R₁] K') = I.map h / J.map h := by
  by_cases H : J = 0
  · rw [H, div_zero, FractionalIdeal.map_zero, div_zero]
  · simp [← coeToSubmodule_inj, div_of_ne_zero H, div_of_ne_zero (map_ne_zero _ H)]
/-
**FractionalIdeal.map_one_div** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：map_one_div (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') : (1 / I).map (h
 : K ->ₐ[R₁] K') = 1 / I.map h
参数：I : FractionalIdeal R₁⁰ K；h : K ≃ₐ[R₁] K'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.map_div`：∀ {R₁ : Type u_3} [inst : CommRing R₁] {K : Typ
e u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K]   [inst_3 : IsFractionRing R₁ 
K] [inst_4 : …
· 使用定理 `FractionalIdeal.map_one`：∀ {R : Type u_1} [inst : CommRing R] {S : Submo
noid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {P' : Type
 u_3} [inst_3…
-/
theorem map_one_div (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    (1 / I).map (h : K →ₐ[R₁] K') = 1 / I.map h := by
  rw [FractionalIdeal.map_div, FractionalIdeal.map_one]

end Quotient

section Field

variable {R₁ K L : Type*} [CommRing R₁] [Field K] [Field L]
variable [Algebra R₁ K] [IsFractionRing R₁ K] [Algebra K L] [IsFractionRing K L]

/-
**FractionalIdeal.eq_zero_or_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：eq_zero_or_one (I : FractionalIdeal K⁰ L) : I = 0 ∨ I = 1
参数：I : FractionalIdeal K⁰ L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsFractionRing.mk'_eq_div`：∀ {A : Type u_4} [inst : CommRing A] {K : Typ
e u_5} [inst_1 : Field K] [inst_2 : Algebra A K]   [inst_3 : IsFractionRing A K]
 {r : A} (s : ↥…
· 使用定理 `FractionalIdeal.exists_ne_zero_mem_isInteger`：exists_ne_zero_mem_isInteg
er [Nontrivial R] (hI : I != 0) : exists x, x != 0 ∧ algebraMap R K x in I
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem eq_zero_or_one (I : FractionalIdeal K⁰ L) : I = 0 ∨ I = 1 := by
  rw [or_iff_not_imp_left]
  intro hI
  simp_rw [@SetLike.ext_iff _ _ _ I 1, mem_one_iff]
  intro x
  constructor
  · intro x_mem
    obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq K⁰ x
    refine ⟨n / d, ?_⟩
    rw [map_div₀, IsFractionRing.mk'_eq_div]
  · rintro ⟨x, rfl⟩
    obtain ⟨y, y_ne, y_mem⟩ := exists_ne_zero_mem_isInteger hI
    rw [← div_mul_cancel₀ x y_ne, map_mul, ← Algebra.smul_def]
    exact smul_mem (M := L) I (x / y) y_mem
/-
**FractionalIdeal.eq_zero_or_one_of_isField** 是 Mathlib 中的一个定理，位于命名空间 `Fractiona
lIdeal`。
形式化陈述：eq_zero_or_one_of_isField (hF : IsField R₁) (I : FractionalIdeal R₁⁰ K) : 
I = 0 ∨ I = 1
参数：hF : IsField R₁；I : FractionalIdeal R₁⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.eq_zero_or_one`：eq_zero_or_one (I : FractionalIdeal K⁰ L
) : I = 0 ∨ I = 1
-/
theorem eq_zero_or_one_of_isField (hF : IsField R₁) (I : FractionalIdeal R₁⁰ K) : I = 0 ∨ I = 1 :=
  letI : Field R₁ := hF.toField
  eq_zero_or_one I

end Field

section PrincipalIdeal

variable {R₁ : Type*} [CommRing R₁] {K : Type*} [Field K]
variable [Algebra R₁ K] [IsFractionRing R₁ K]

variable (R₁)

/-- `FractionalIdeal.span_finset R₁ s f` is the fractional ideal of `R₁` generated by `f '' s`. -/
-- Porting note: `@[simps]` generated a `Subtype.val` coercion instead of a
-- `FractionalIdeal.coeToSubmodule` coercion
/-
**FractionalIdeal.spanFinset** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：spanFinset {ι : Type*} (s : Finset ι) (f : ι -> K) : FractionalIdeal R₁⁰ K
参数：s : Finset ι；f : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def spanFinset {ι : Type*} (s : Finset ι) (f : ι → K) : FractionalIdeal R₁⁰ K :=
  ⟨Submodule.span R₁ (f '' s), by
    obtain ⟨a', ha'⟩ := IsLocalization.exist_integer_multiples R₁⁰ s f
    refine ⟨a', a'.2, fun x hx => Submodule.span_induction ?_ ?_ ?_ ?_ hx⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact ha' i hi
    · rw [smul_zero]
      exact IsLocalization.isInteger_zero
    · intro x y _ _ hx hy
      rw [smul_add]
      exact IsLocalization.isInteger_add hx hy
    · intro c x _ hx
      rw [smul_comm]
      exact IsLocalization.isInteger_smul hx⟩
/-
**FractionalIdeal.spanFinset_coe** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：∀ (R₁ : Type u_3) [inst : CommRing R₁] {K : Type u_4} [inst_1 : Field K] [
inst_2 : Algebra R₁ K]   [inst_3 : IsFractionRing R₁ K] {ι : Type u_5} (s : Fins
et ι) (f : ι → K),   ↑(FractionalIdeal.spanFinset R₁ s f) = Submodule.span R₁ (f
 '' ↑s)
参数：R₁ : Type u_3；s : Finset ι；f : ι → K；FractionalIdeal.spanFinset R₁ s f；f '' ↑
s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma spanFinset_coe {ι : Type*} (s : Finset ι) (f : ι → K) :
    (spanFinset R₁ s f : Submodule R₁ K) = Submodule.span R₁ (f '' s) :=
  rfl

variable {R₁}

@[simp]
/-
**FractionalIdeal.spanFinset_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：spanFinset_eq_zero {ι : Type*} {s : Finset ι} {f : ι -> K} : spanFinset R₁
 s f = 0 ↔ forall j in s, f j = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem spanFinset_eq_zero {ι : Type*} {s : Finset ι} {f : ι → K} :
    spanFinset R₁ s f = 0 ↔ ∀ j ∈ s, f j = 0 := by
  simp only [← coeToSubmodule_inj, spanFinset_coe, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, Finset.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
/-
**FractionalIdeal.spanFinset_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：spanFinset_ne_zero {ι : Type*} {s : Finset ι} {f : ι -> K} : spanFinset R₁
 s f != 0 ↔ exists j in s, f j != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem spanFinset_ne_zero {ι : Type*} {s : Finset ι} {f : ι → K} :
    spanFinset R₁ s f ≠ 0 ↔ ∃ j ∈ s, f j ≠ 0 := by simp

open Submodule.IsPrincipal

variable [IsLocalization S P]
/-
**FractionalIdeal.isFractional_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Fractio
nalIdeal`。
形式化陈述：isFractional_span_singleton (x : P) : IsFractional S (span R {x} : Submodu
le R P)
参数：x : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.exists_integer_multiple`：exists_integer_multiple (a : S) 
: exists b : M, IsInteger R ((b : R) • a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.isFractional_span_iff`：isFractional_span_iff {s : Set P}
 : IsFractional S (span R s) ↔ exists a in S, forall b : P, b in s -> IsInteger 
R (a • b)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem isFractional_span_singleton (x : P) : IsFractional S (span R {x} : Submodule R P) :=
  let ⟨a, ha⟩ := exists_integer_multiple S x
  isFractional_span_iff.mpr ⟨a, a.2, fun _ hx' => (Set.mem_singleton_iff.mp hx').symm ▸ ha⟩

variable (S)

/-- `spanSingleton x` is the fractional ideal generated by `x` if `0 ∉ S` -/
irreducible_def spanSingleton (x : P) : FractionalIdeal S P :=
  ⟨span R {x}, isFractional_span_singleton x⟩

-- local attribute [semireducible] span_singleton
@[simp]
/-
**FractionalIdeal.coe_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：coe_spanSingleton (x : P) : (spanSingleton S x : Submodule R P) = span R {
x}
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional_span_singleton`：isFractional_span_singleton
 (x : P) : IsFractional S (span R {x} : Submodule R P)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.spanSingleton_def`：∀ {R : Type u_5} [inst : CommRing R] 
(S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra R P]   
[inst_3 : IsLocalizatio…
-/
theorem coe_spanSingleton (x : P) : (spanSingleton S x : Submodule R P) = span R {x} := by
  rw [spanSingleton]
  rfl

@[simp]
/-
**FractionalIdeal.mem_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_spanSingleton {x y : P} : x in spanSingleton S y ↔ exists z : R, z • y
 = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional_span_singleton`：isFractional_span_singleton
 (x : P) : IsFractional S (span R {x} : Submodule R P)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.spanSingleton_def`：∀ {R : Type u_5} [inst : CommRing R] 
(S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra R P]   
[inst_3 : IsLocalizatio…
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
-/
theorem mem_spanSingleton {x y : P} : x ∈ spanSingleton S y ↔ ∃ z : R, z • y = x := by
  rw [spanSingleton]
  exact Submodule.mem_span_singleton
/-
**FractionalIdeal.mem_spanSingleton_self** 是 Mathlib 中的一个定理，位于命名空间 `FractionalId
eal`。
形式化陈述：mem_spanSingleton_self (x : P) : x in spanSingleton S x
参数：x : P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mem_spanSingleton`：mem_spanSingleton {x y : P} : x in sp
anSingleton S y ↔ exists z : R, z • y = x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem mem_spanSingleton_self (x : P) : x ∈ spanSingleton S x :=
  (mem_spanSingleton S).mpr ⟨1, one_smul _ _⟩

set_option backward.isDefEq.respectTransparency false in
variable (P) in
/-- A version of `FractionalIdeal.den_mul_self_eq_num` in terms of fractional ideals. -/
/-
**FractionalIdeal.den_mul_self_eq_num'** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdea
l`。
形式化陈述：den_mul_self_eq_num' (I : FractionalIdeal S P) : spanSingleton S (algebraM
ap R P I.den) * I = I.num
参数：I : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `FractionalIdeal.coe_spanSingleton`：coe_spanSingleton (x : P) : (spanSing
leton S x : Submodule R P) = span R {x}
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `Submodule.span_singleton_mul`：span_singleton_mul {x : A} {p : Submodule 
R A} : Submodule.span R {x} * p = x • p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Submodule.mem_smul_pointwise_iff_exists`：mem_smul_pointwise_iff_exists (
m : M) (a : α) (S : Submodule R M) : m in a • S ↔ exists b in S, a • b = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `FractionalIdeal.den_mul_self_eq_num`：den_mul_self_eq_num (I : Fractional
Ideal S P) : I.den • (I : Submodule R P) = Submodule.map (Algebra.linearMap R P)
 I.num

--- 原说明 ---
A version of `FractionalIdeal.den_mul_self_eq_num` in terms of fractional ideals
.
-/
theorem den_mul_self_eq_num' (I : FractionalIdeal S P) :
    spanSingleton S (algebraMap R P I.den) * I = I.num := by
  apply coeToSubmodule_injective
  dsimp only
  rw [coe_mul, ← smul_eq_mul, coe_spanSingleton, smul_eq_mul, Submodule.span_singleton_mul]
  convert! I.den_mul_self_eq_num using 1
  ext
  rw [mem_smul_pointwise_iff_exists, mem_smul_pointwise_iff_exists]
  simp [smul_eq_mul, Algebra.smul_def, Submonoid.smul_def]

variable {S}

@[simp]
/-
**FractionalIdeal.spanSingleton_le_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Fractional
Ideal`。
形式化陈述：spanSingleton_le_iff_mem {x : P} {I : FractionalIdeal S P} : spanSingleton
 S x <= I ↔ x in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coe_le_coe`：coe_le_coe {I J : FractionalIdeal S P} : (I 
: Submodule R P) <= (J : Submodule R P) ↔ I <= J
· 使用定理 `FractionalIdeal.coe_spanSingleton`：coe_spanSingleton (x : P) : (spanSing
leton S x : Submodule R P) = span R {x}
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `FractionalIdeal.mem_coe`：mem_coe {I : FractionalIdeal S P} {x : P} : x i
n (I : Submodule R P) ↔ x in I
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem spanSingleton_le_iff_mem {x : P} {I : FractionalIdeal S P} :
    spanSingleton S x ≤ I ↔ x ∈ I := by
  rw [← coe_le_coe, coe_spanSingleton, Submodule.span_singleton_le_iff_mem, mem_coe]
/-
**FractionalIdeal.spanSingleton_eq_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Frac
tionalIdeal`。
形式化陈述：spanSingleton_eq_spanSingleton [IsDomain R] [Module.IsTorsionFree R P] {x 
y : P} : spanSingleton S x = spanSingleton S y ↔ exists z : Rˣ, z • x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_singleton_eq_span_singleton`：span_singleton_eq_span_singl
eton {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.I
sTorsionFree R M] {x y : M} : (R…
· 使用定理 `FractionalIdeal.isFractional_span_singleton`：isFractional_span_singleton
 (x : P) : IsFractional S (span R {x} : Submodule R P)
· 使用定理 `FractionalIdeal.spanSingleton_def`：∀ {R : Type u_5} [inst : CommRing R] 
(S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra R P]   
[inst_3 : IsLocalizatio…
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
-/
theorem spanSingleton_eq_spanSingleton [IsDomain R] [Module.IsTorsionFree R P] {x y : P} :
    spanSingleton S x = spanSingleton S y ↔ ∃ z : Rˣ, z • x = y := by
  rw [← Submodule.span_singleton_eq_span_singleton, spanSingleton, spanSingleton]
  exact Subtype.mk_eq_mk

set_option backward.isDefEq.respectTransparency false in
/-
**FractionalIdeal.eq_spanSingleton_of_principal** 是 Mathlib 中的一个定理，位于命名空间 `Fract
ionalIdeal`。
形式化陈述：eq_spanSingleton_of_principal (I : FractionalIdeal S P) [IsPrincipal (I : 
Submodule R P)] : I = spanSingleton S (generator (I : Submodule R P))
参数：I : FractionalIdeal S P；I : Submodule R P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional_span_singleton`：isFractional_span_singleton
 (x : P) : IsFractional S (span R {x} : Submodule R P)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.spanSingleton_def`：∀ {R : Type u_5} [inst : CommRing R] 
(S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra R P]   
[inst_3 : IsLocalizatio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coeToSubmodule_inj`：coeToSubmodule_inj {I J : Fractional
Ideal S P} : (I : Submodule R P) = J ↔ I = J
· 使用定理 `FractionalIdeal.coe_mk`：coe_mk (I : Submodule R P) (hI : IsFractional S 
I) : coeToSubmodule ⟨I, hI⟩ = I
· 使用定理 `Submodule.IsPrincipal.span_singleton_generator`：span_singleton_generator
 (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S
-/
theorem eq_spanSingleton_of_principal (I : FractionalIdeal S P) [IsPrincipal (I : Submodule R P)] :
    I = spanSingleton S (generator (I : Submodule R P)) := by
  -- Porting note: this used to be `coeToSubmodule_injective (span_singleton_generator ↑I).symm`
  -- but Lean 4 struggled to unify everything. Turned it into an explicit `rw`.
  rw [spanSingleton, ← coeToSubmodule_inj, coe_mk, span_singleton_generator]
/-
**FractionalIdeal.isPrincipal_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：isPrincipal_iff (I : FractionalIdeal S P) : IsPrincipal (I : Submodule R P
) ↔ exists x, I = spanSingleton S x
参数：I : FractionalIdeal S P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.eq_spanSingleton_of_principal`：eq_spanSingleton_of_princ
ipal (I : FractionalIdeal S P) [IsPrincipal (I : Submodule R P)] : I = spanSingl
eton S (generator (I : Submodule R …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `FractionalIdeal.coe_spanSingleton`：coe_spanSingleton (x : P) : (spanSing
leton S x : Submodule R P) = span R {x}
-/
theorem isPrincipal_iff (I : FractionalIdeal S P) :
    IsPrincipal (I : Submodule R P) ↔ ∃ x, I = spanSingleton S x :=
  ⟨fun _ => ⟨generator (I : Submodule R P), eq_spanSingleton_of_principal I⟩,
    fun ⟨x, hx⟩ => { principal := ⟨x, Eq.trans (congr_arg _ hx) (coe_spanSingleton _ x)⟩ }⟩

@[simp]
/-
**FractionalIdeal.spanSingleton_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：spanSingleton_zero : spanSingleton S (0 : P) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem spanSingleton_zero : spanSingleton S (0 : P) = 0 := by
  ext
  simp [eq_comm]
/-
**FractionalIdeal.spanSingleton_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fractiona
lIdeal`。
形式化陈述：spanSingleton_eq_zero_iff {y : P} : spanSingleton S y = 0 ↔ y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.span_eq_bot`：span_eq_bot : span R (s : Set M) = ⊥ ↔ forall x i
n s, (x : M) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coe_spanSingleton`：coe_spanSingleton (x : P) : (spanSing
leton S x : Submodule R P) = span R {x}
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FractionalIdeal.spanSingleton.congr_simp`：∀ {R : Type u_5} [inst : CommR
ing R] (S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra 
R P]   [inst_3 : IsLocalizatio…
· 使用定理 `FractionalIdeal.spanSingleton_zero`：spanSingleton_zero : spanSingleton S
 (0 : P) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem spanSingleton_eq_zero_iff {y : P} : spanSingleton S y = 0 ↔ y = 0 :=
  ⟨fun h =>
    span_eq_bot.mp (by simpa using congr_arg Subtype.val h : span R {y} = ⊥) y (mem_singleton y),
    fun h => by simp [h]⟩
/-
**FractionalIdeal.spanSingleton_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fractiona
lIdeal`。
形式化陈述：spanSingleton_ne_zero_iff {y : P} : spanSingleton S y != 0 ↔ y != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `FractionalIdeal.spanSingleton_eq_zero_iff`：spanSingleton_eq_zero_iff {y 
: P} : spanSingleton S y = 0 ↔ y = 0
-/
theorem spanSingleton_ne_zero_iff {y : P} : spanSingleton S y ≠ 0 ↔ y ≠ 0 :=
  not_congr spanSingleton_eq_zero_iff

@[simp]
/-
**FractionalIdeal.spanSingleton_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：spanSingleton_one : spanSingleton S (1 : P) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FractionalIdeal.mem_spanSingleton`：mem_spanSingleton {x y : P} : x in sp
anSingleton S y ↔ exists z : R, z • y = x
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
-/
theorem spanSingleton_one : spanSingleton S (1 : P) = 1 := by
  ext
  refine (mem_spanSingleton S).trans ((exists_congr ?_).trans (mem_one_iff S).symm)
  intro x'
  rw [Algebra.smul_def, mul_one]

@[simp]
/-
**FractionalIdeal.spanSingleton_mul_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Fra
ctionalIdeal`。
形式化陈述：spanSingleton_mul_spanSingleton (x y : P) : spanSingleton S x * spanSingle
ton S y = spanSingleton S (x * y)
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `FractionalIdeal.coe_spanSingleton`：coe_spanSingleton (x : P) : (spanSing
leton S x : Submodule R P) = span R {x}
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `Set.singleton_mul_singleton`：singleton_mul_singleton : ({a} : Set α) * {
b} = {a * b}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem spanSingleton_mul_spanSingleton (x y : P) :
    spanSingleton S x * spanSingleton S y = spanSingleton S (x * y) := by
  apply coeToSubmodule_injective
  simp only [coe_mul, coe_spanSingleton, span_mul_span, singleton_mul_singleton]

@[simp]
/-
**FractionalIdeal.spanSingleton_pow** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：spanSingleton_pow (x : P) (n : Nat) : spanSingleton S x ^ n = spanSingleto
n S (x ^ n)
参数：x : P；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `FractionalIdeal.spanSingleton_mul_spanSingleton`：spanSingleton_mul_spanS
ingleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x 
* y)
-/
theorem spanSingleton_pow (x : P) (n : ℕ) : spanSingleton S x ^ n = spanSingleton S (x ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, spanSingleton_one]
  | succ n hn => rw [pow_succ, hn, spanSingleton_mul_spanSingleton, pow_succ]

@[simp]
/-
**FractionalIdeal.coeIdeal_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
形式化陈述：coeIdeal_span_singleton (x : R) : (↑(Ideal.span {x} : Ideal R) : Fractiona
lIdeal S P) = spanSingleton S (algebraMap R P x)
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FractionalIdeal.mem_coeIdeal`：mem_coeIdeal {x : P} {I : Ideal R} : x in 
(I : FractionalIdeal S P) ↔ exists x', x' in I ∧ algebraMap R P x' = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FractionalIdeal.mem_spanSingleton`：mem_spanSingleton {x y : P} : x in sp
anSingleton S y ↔ exists z : R, z • y = x
-/
theorem coeIdeal_span_singleton (x : R) :
    (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebraMap R P x) := by
  ext y
  refine (mem_coeIdeal S).trans (Iff.trans ?_ (mem_spanSingleton S).symm)
  constructor
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.mp hy'
    use x'
    rw [smul_eq_mul, map_mul, Algebra.smul_def]
  · rintro ⟨y', rfl⟩
    refine ⟨y' * x, Submodule.mem_span_singleton.mpr ⟨y', rfl⟩, ?_⟩
    rw [map_mul, Algebra.smul_def]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FractionalIdeal.canonicalEquiv_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Fracti
onalIdeal`。
形式化陈述：canonicalEquiv_spanSingleton {P'} [CommRing P'] [Algebra R P'] [IsLocaliza
tion S P'] (x : P) : canonicalEquiv S P P' (spanSingleton S x) = spanSingleton S
 (IsLocalization.map P' (RingHom.id R) (fun y (hy : y in S) => show RingHom.id R
 y in S from hy) x)
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.mem_spanSingleton`：mem_spanSingleton {x y : P} : x in sp
anSingleton S y ↔ exists z : R, z • y = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_canonicalEquiv_apply`：mem_canonicalEquiv_apply {I : 
FractionalIdeal S P} {x : P'} : x in canonicalEquiv S P P' I ↔ exists y in I, Is
Localization.map P' (RingHom.i…
· 使用定理 `IsLocalization.map_smul`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] {P
 : Type u_3} …
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem canonicalEquiv_spanSingleton {P'} [CommRing P'] [Algebra R P'] [IsLocalization S P']
    (x : P) :
    canonicalEquiv S P P' (spanSingleton S x) =
      spanSingleton S
        (IsLocalization.map P' (RingHom.id R)
          (fun y (hy : y ∈ S) => show RingHom.id R y ∈ S from hy) x) := by
  apply SetLike.ext_iff.mpr
  intro y
  constructor <;> intro h
  · rw [mem_spanSingleton]
    obtain ⟨x', hx', rfl⟩ := (mem_canonicalEquiv_apply _ _ _).mp h
    obtain ⟨z, rfl⟩ := (mem_spanSingleton _).mp hx'
    use z
    rw [IsLocalization.map_smul, RingHom.id_apply]
  · rw [mem_canonicalEquiv_apply]
    obtain ⟨z, rfl⟩ := (mem_spanSingleton _).mp h
    use z • x
    use (mem_spanSingleton _).mpr ⟨z, rfl⟩
    simp [IsLocalization.map_smul]
/-
**FractionalIdeal.mem_singleton_mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_singleton_mul {x y : P} {I : FractionalIdeal S P} : y in spanSingleton
 S x * I ↔ exists y' in I, y = x * y'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.mul_induction_on`：∀ {R : Type u_1} [inst : CommRing R] {
S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {
I J : FractionalIdeal …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_spanSingleton`：mem_spanSingleton {x y : P} : x in sp
anSingleton S y ↔ exists z : R, z • y = x
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `FractionalIdeal.mul_mem_mul`：mul_mem_mul {I J : FractionalIdeal S P} {i 
j : P} (hi : i in I) (hj : j in J) : i * j in I * J
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem mem_singleton_mul {x y : P} {I : FractionalIdeal S P} :
    y ∈ spanSingleton S x * I ↔ ∃ y' ∈ I, y = x * y' := by
  constructor
  · intro h
    refine FractionalIdeal.mul_induction_on h ?_ ?_
    · intro x' hx' y' hy'
      obtain ⟨a, ha⟩ := (mem_spanSingleton S).mp hx'
      use a • y', Submodule.smul_mem (I : Submodule R P) a hy'
      rw [← ha, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    · rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
      exact ⟨y + y', Submodule.add_mem (I : Submodule R P) hy hy', (mul_add _ _ _).symm⟩
  · rintro ⟨y', hy', rfl⟩
    exact mul_mem_mul ((mem_spanSingleton S).mpr ⟨1, one_smul _ _⟩) hy'

variable (K) in
/-
**FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Fracti
onalIdeal`。
形式化陈述：∀ {R₁ : Type u_3} [inst : CommRing R₁] (K : Type u_4) [inst_1 : Field K] [
inst_2 : Algebra R₁ K]   [inst_3 : IsFractionRing R₁ K] {I J : Ideal R₁} {x y : 
R₁} (hy : y ∈ nonZeroDivisors R₁),   FractionalIdeal.spanSingleton (nonZeroDivis
ors R₁) (IsLocalization.mk' K x ⟨y, hy⟩) * ↑I = ↑J ↔     Ideal.span {x} * I = Id
eal.span {y} * J
参数：K : Type u_4；hy : y ∈ nonZeroDivisors R₁；nonZeroDivisors R₁；IsLocalization.mk
' K x ⟨y, hy⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.spanSingleton_mul_spanSingleton`：spanSingleton_mul_spanS
ingleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x 
* y)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_eq_mul_mk'_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coeIdeal_mul`：coeIdeal_mul (I J : Ideal R) : (↑(I * J) :
 FractionalIdeal S P) = I * J
· 使用定理 `FractionalIdeal.coeIdeal_span_singleton`：coeIdeal_span_singleton (x : R)
 : (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebr
aMap R P x)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Units.mul_right_inj`：mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a 
* c ↔ b = c
· 使用定理 `FractionalIdeal.coeIdeal_inj`：coeIdeal_inj {I J : Ideal R} : (I : Fracti
onalIdeal R⁰ K) = (J : FractionalIdeal R⁰ K) ↔ I = J
-/
theorem mk'_mul_coeIdeal_eq_coeIdeal {I J : Ideal R₁} {x y : R₁} (hy : y ∈ R₁⁰) :
    spanSingleton R₁⁰ (IsLocalization.mk' K x ⟨y, hy⟩) * I = (J : FractionalIdeal R₁⁰ K) ↔
      Ideal.span {x} * I = Ideal.span {y} * J := by
  have :
    spanSingleton R₁⁰ (IsLocalization.mk' _ (1 : R₁) ⟨y, hy⟩) *
        spanSingleton R₁⁰ (algebraMap R₁ K y) =
      1 := by
    rw [spanSingleton_mul_spanSingleton, mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one,
      IsLocalization.mk'_self, spanSingleton_one]
  let y' : (FractionalIdeal R₁⁰ K)ˣ := Units.mkOfMulEqOne _ _ this
  have coe_y' : ↑y' = spanSingleton R₁⁰ (IsLocalization.mk' K (1 : R₁) ⟨y, hy⟩) := rfl
  refine Iff.trans ?_ (y'.mul_right_inj.trans coeIdeal_inj)
  rw [coe_y', coeIdeal_mul, coeIdeal_span_singleton, coeIdeal_mul, coeIdeal_span_singleton, ←
    mul_assoc, spanSingleton_mul_spanSingleton, ← mul_assoc, spanSingleton_mul_spanSingleton,
    mul_comm (mk' _ _ _), ← IsLocalization.mk'_eq_mul_mk'_one, mul_comm (mk' _ _ _), ←
    IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_self, spanSingleton_one, one_mul]
/-
**FractionalIdeal.spanSingleton_mul_coeIdeal_eq_coeIdeal** 是 Mathlib 中的一个定理，位于命名
空间 `FractionalIdeal`。
形式化陈述：spanSingleton_mul_coeIdeal_eq_coeIdeal {I J : Ideal R₁} {z : K} : spanSing
leton R₁⁰ z * (I : FractionalIdeal R₁⁰ K) = J ↔ Ideal.span {((IsLocalization.sec
 R₁⁰ z).1 : R₁)} * I = Ideal.span {((IsLocalization.sec R₁⁰ z).2 : R₁)} * J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal`：∀ {R₁ : Type u_3} [inst : 
CommRing R₁] (K : Type u_4) [inst_1 : Field K] [inst_2 : Algebra R₁ K]   [inst_3
 : IsFractionRing R₁ K] {I J : Ide…
· 使用定理 `IsLocalization.mk'_sec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem spanSingleton_mul_coeIdeal_eq_coeIdeal {I J : Ideal R₁} {z : K} :
    spanSingleton R₁⁰ z * (I : FractionalIdeal R₁⁰ K) = J ↔
      Ideal.span {((IsLocalization.sec R₁⁰ z).1 : R₁)} * I =
        Ideal.span {((IsLocalization.sec R₁⁰ z).2 : R₁)} * J := by
  rw [← mk'_mul_coeIdeal_eq_coeIdeal K (IsLocalization.sec R₁⁰ z).2.prop,
    IsLocalization.mk'_sec K z]

variable [IsDomain R₁]
/-
**FractionalIdeal.one_div_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：one_div_spanSingleton (x : K) : 1 / spanSingleton R₁⁰ x = spanSingleton R₁
⁰ x⁻¹
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.spanSingleton.congr_simp`：∀ {R : Type u_5} [inst : CommR
ing R] (S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra 
R P]   [inst_3 : IsLocalizatio…
· 使用定理 `FractionalIdeal.spanSingleton_zero`：spanSingleton_zero : spanSingleton S
 (0 : P) = 0
· 使用定理 `FractionalIdeal.div_zero`：div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 =
 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.eq_one_div_of_mul_eq_one_right`：eq_one_div_of_mul_eq_one
_right (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = 1 / I
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FractionalIdeal.spanSingleton_mul_spanSingleton`：spanSingleton_mul_spanS
ingleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x 
* y)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
-/
theorem one_div_spanSingleton (x : K) : 1 / spanSingleton R₁⁰ x = spanSingleton R₁⁰ x⁻¹ := by
  classical
  exact if h : x = 0 then by simp [h] else (eq_one_div_of_mul_eq_one_right _ _ (by simp [h])).symm

@[simp]
/-
**FractionalIdeal.div_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：div_spanSingleton (J : FractionalIdeal R₁⁰ K) (d : K) : J / spanSingleton 
R₁⁰ d = spanSingleton R₁⁰ d⁻¹ * J
参数：J : FractionalIdeal R₁⁰ K；d : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.one_div_spanSingleton`：one_div_spanSingleton (x : K) : 1
 / spanSingleton R₁⁰ x = spanSingleton R₁⁰ x⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FractionalIdeal.spanSingleton.congr_simp`：∀ {R : Type u_5} [inst : CommR
ing R] (S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra 
R P]   [inst_3 : IsLocalizatio…
· 使用定理 `FractionalIdeal.spanSingleton_zero`：spanSingleton_zero : spanSingleton S
 (0 : P) = 0
· 使用定理 `FractionalIdeal.div_zero`：div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 =
 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.spanSingleton_eq_zero_iff`：spanSingleton_eq_zero_iff {y 
: P} : spanSingleton S y = 0 ↔ y = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 56 条，此处仅展示前 30 条）
-/
theorem div_spanSingleton (J : FractionalIdeal R₁⁰ K) (d : K) :
    J / spanSingleton R₁⁰ d = spanSingleton R₁⁰ d⁻¹ * J := by
  rw [← one_div_spanSingleton]
  by_cases hd : d = 0
  · simp only [hd, spanSingleton_zero, div_zero, zero_mul]
  have h_spand : spanSingleton R₁⁰ d ≠ 0 := mt spanSingleton_eq_zero_iff.mp hd
  apply le_antisymm
  · intro x hx
    rw [← mem_coe, coe_div h_spand, Submodule.mem_div_iff_forall_mul_mem] at hx
    specialize hx d (mem_spanSingleton_self R₁⁰ d)
    have h_xd : x = d⁻¹ * (x * d) := by field
    rw [← mem_coe, coe_mul, one_div_spanSingleton, h_xd]
    exact Submodule.mul_mem_mul (mem_spanSingleton_self R₁⁰ _) hx
  · rw [le_div_iff_mul_le h_spand, mul_assoc, mul_left_comm, one_div_spanSingleton,
      spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hd, spanSingleton_one, mul_one]
/-
**FractionalIdeal.exists_eq_spanSingleton_mul** 是 Mathlib 中的一个定理，位于命名空间 `Fractio
nalIdeal`。
形式化陈述：exists_eq_spanSingleton_mul (I : FractionalIdeal R₁⁰ K) : exists (a : R₁) 
(aI : Ideal R₁), a != 0 ∧ I = spanSingleton R₁⁰ (algebraMap R₁ K a)⁻¹ * aI
参数：I : FractionalIdeal R₁⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   (I : 
FractionalIdeal S …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `IsFractionRing.to_map_eq_zero_iff`：to_map_eq_zero_iff {x : R} : algebraM
ap R K x = 0 ↔ x = 0
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mem_coeIdeal`：mem_coeIdeal {x : P} {I : Ideal R} : x in 
(I : FractionalIdeal S P) ↔ exists x', x' in I ∧ algebraMap R P x' = x
· 使用定理 `FractionalIdeal.mem_singleton_mul`：mem_singleton_mul {x y : P} {I : Frac
tionalIdeal S P} : y in spanSingleton S x * I ↔ exists y' in I, y = x * y'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Algebra.linearMap_apply`：linearMap_apply (r : R) : Algebra.linearMap R A
 r = algebraMap R A r
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem exists_eq_spanSingleton_mul (I : FractionalIdeal R₁⁰ K) :
    ∃ (a : R₁) (aI : Ideal R₁), a ≠ 0 ∧ I = spanSingleton R₁⁰ (algebraMap R₁ K a)⁻¹ * aI := by
  obtain ⟨a_inv, nonzero, ha⟩ := I.isFractional
  have nonzero := mem_nonZeroDivisors_iff_ne_zero.mp nonzero
  have map_a_nonzero : algebraMap R₁ K a_inv ≠ 0 :=
    mt IsFractionRing.to_map_eq_zero_iff.mp nonzero
  refine
    ⟨a_inv,
      Submodule.comap (Algebra.linearMap R₁ K) ↑(spanSingleton R₁⁰ (algebraMap R₁ K a_inv) * I),
      nonzero, ext fun x => Iff.trans ⟨?_, ?_⟩ mem_singleton_mul.symm⟩
  · intro hx
    obtain ⟨x', hx'⟩ := ha x hx
    rw [Algebra.smul_def] at hx'
    refine ⟨algebraMap R₁ K x', (mem_coeIdeal _).mpr ⟨x', mem_singleton_mul.mpr ?_, rfl⟩, ?_⟩
    · exact ⟨x, hx, hx'⟩
    · rw [hx', ← mul_assoc, inv_mul_cancel₀ map_a_nonzero, one_mul]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x', hx', rfl⟩ := (mem_coeIdeal _).mp hy
    obtain ⟨y', hy', hx'⟩ := mem_singleton_mul.mp hx'
    rw [Algebra.linearMap_apply] at hx'
    rwa [hx', ← mul_assoc, inv_mul_cancel₀ map_a_nonzero, one_mul]


/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `J` is nonzero. -/
/-
**FractionalIdeal.ideal_factor_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdea
l`。
形式化陈述：ideal_factor_ne_zero {R} [CommRing R] {K : Type*} [Field K] [Algebra R K] 
[IsFractionRing R K] {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R} {J : Ideal
 R} (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) : J != 0
参数：hI : I != 0；haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `FractionalIdeal.coeIdeal_bot`：coeIdeal_bot : ((⊥ : Ideal R) : Fractional
Ideal S P) = 0
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥

--- 原说明 ---
If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such t
hat
`I = a⁻¹J`, then `J` is nonzero.
-/
theorem ideal_factor_ne_zero {R} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {a : R} {J : Ideal R}
    (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) : J ≠ 0 := fun h ↦ by
  rw [h, Ideal.zero_eq_bot, coeIdeal_bot, mul_zero] at haJ
  exact hI haJ

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `a` is nonzero. -/
/-
**FractionalIdeal.constant_factor_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
形式化陈述：constant_factor_ne_zero {R} [CommRing R] {K : Type*} [Field K] [Algebra R 
K] [IsFractionRing R K] {I : FractionalIdeal R⁰ K} (hI : I != 0) {a : R} {J : Id
eal R} (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) : (Ideal.span {a
} : Ideal R) != 0
参数：hI : I != 0；haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `FractionalIdeal.spanSingleton_zero`：spanSingleton_zero : spanSingleton S
 (0 : P) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥

--- 原说明 ---
If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such t
hat
`I = a⁻¹J`, then `a` is nonzero.
-/
theorem constant_factor_ne_zero {R} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {a : R} {J : Ideal R}
    (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    (Ideal.span {a} : Ideal R) ≠ 0 := fun h ↦ by
  rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h
  rw [h, map_zero, inv_zero, spanSingleton_zero, zero_mul] at haJ
  exact hI haJ
/-
**FractionalIdeal.isPrincipal** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
形式化陈述：isPrincipal {R} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebr
a R K] [IsFractionRing R K] (I : FractionalIdeal R⁰ K) : (I : Submodule R K).IsP
rincipal
参数：I : FractionalIdeal R⁰ K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.exists_eq_spanSingleton_mul`：exists_eq_spanSingleton_mul
 (I : FractionalIdeal R₁⁰ K) : exists (a : R₁) (aI : Ideal R₁), a != 0 ∧ I = spa
nSingleton R₁⁰ (algebraMap R₁ K a…
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsPrincipal.span_singleton_generator`：span_singleton_generator
 (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `FractionalIdeal.coeIdeal_span_singleton`：coeIdeal_span_singleton (x : R)
 : (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebr
aMap R P x)
· 使用定理 `FractionalIdeal.spanSingleton_mul_spanSingleton`：spanSingleton_mul_spanS
ingleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x 
* y)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `FractionalIdeal.isFractional_span_singleton`：isFractional_span_singleton
 (x : P) : IsFractional S (span R {x} : Submodule R P)
· 使用定理 `FractionalIdeal.spanSingleton_def`：∀ {R : Type u_5} [inst : CommRing R] 
(S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra R P]   
[inst_3 : IsLocalizatio…
-/
instance isPrincipal {R} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) : (I : Submodule R K).IsPrincipal := by
  obtain ⟨a, aI, -, ha⟩ := exists_eq_spanSingleton_mul I
  use (algebraMap R K a)⁻¹ * algebraMap R K (generator aI)
  suffices I = spanSingleton R⁰ ((algebraMap R K a)⁻¹ * algebraMap R K (generator aI)) by
    rw [spanSingleton] at this
    exact congr_arg Subtype.val this
  conv_lhs => rw [ha, ← span_singleton_generator aI]
  rw [Ideal.submodule_span_eq, coeIdeal_span_singleton (generator aI),
    spanSingleton_mul_spanSingleton]
/-
**FractionalIdeal.le_spanSingleton_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fractional
Ideal`。
形式化陈述：le_spanSingleton_mul_iff {x : P} {I J : FractionalIdeal S P} : I <= spanSi
ngleton S x * J ↔ forall zI in I, exists zJ in J, x * zJ = zI
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_spanSingleton_mul_iff {x : P} {I J : FractionalIdeal S P} :
    I ≤ spanSingleton S x * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI :=
  show (∀ {zI} (_ : zI ∈ I), zI ∈ spanSingleton _ x * J) ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI by
    simp only [mem_singleton_mul, eq_comm]
/-
**FractionalIdeal.spanSingleton_mul_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fractional
Ideal`。
形式化陈述：spanSingleton_mul_le_iff {x : P} {I J : FractionalIdeal S P} : spanSinglet
on _ x * I <= J ↔ forall z in I, x * z in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem spanSingleton_mul_le_iff {x : P} {I J : FractionalIdeal S P} :
    spanSingleton _ x * I ≤ J ↔ ∀ z ∈ I, x * z ∈ J := by
  simp only [mul_le, mem_spanSingleton]
  constructor
  · intro h zI hzI
    exact h x ⟨1, one_smul _ _⟩ zI hzI
  · rintro h _ ⟨z, rfl⟩ zI hzI
    rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem J.1 _ (h zI hzI)
/-
**FractionalIdeal.eq_spanSingleton_mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdea
l`。
形式化陈述：eq_spanSingleton_mul {x : P} {I J : FractionalIdeal S P} : I = spanSinglet
on _ x * J ↔ (forall zI in I, exists zJ in J, x * zJ = zI) ∧ forall z in J, x * 
z in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_spanSingleton_mul {x : P} {I J : FractionalIdeal S P} :
    I = spanSingleton _ x * J ↔ (∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI) ∧ ∀ z ∈ J, x * z ∈ I := by
  simp only [le_antisymm_iff, le_spanSingleton_mul_iff, spanSingleton_mul_le_iff]
/-
**FractionalIdeal.num_le** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：num_le (I : FractionalIdeal S P) : (I.num : FractionalIdeal S P) <= I
参数：I : FractionalIdeal S P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.den_mul_self_eq_num'`：den_mul_self_eq_num' (I : Fraction
alIdeal S P) : spanSingleton S (algebraMap R P I.den) * I = I.num
· 使用定理 `FractionalIdeal.spanSingleton_mul_le_iff`：spanSingleton_mul_le_iff {x : 
P} {I J : FractionalIdeal S P} : spanSingleton _ x * I <= J ↔ forall z in I, x *
 z in J
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem num_le (I : FractionalIdeal S P) :
    (I.num : FractionalIdeal S P) ≤ I := by
  rw [← I.den_mul_self_eq_num', spanSingleton_mul_le_iff]
  intro _ h
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ h

/-- If the numerator ideal of a fractional ideal is principal, then so is the fractional ideal. -/
/-
**FractionalIdeal.isPrincipal_of_isPrincipal_num** 是 Mathlib 中的一个定理，位于命名空间 `Frac
tionalIdeal`。
形式化陈述：isPrincipal_of_isPrincipal_num [IsDomain R] (I : FractionalIdeal R⁰ (Fract
ionRing R)) (hI : I.num.IsPrincipal) : (I : Submodule R (FractionRing R)).IsPrin
cipal
参数：I : FractionalIdeal R⁰ (FractionRing R)；hI : I.num.IsPrincipal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.isPrincipal_submodule_iff`：Module.isPrincipal_submodule_iff {p : 
Submodule R M} : IsPrincipal R p ↔ p.IsPrincipal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.isPrincipal_iff`：LinearEquiv.isPrincipal_iff (e : M ≃ₗ[R] M₂
) : Module.IsPrincipal R M ↔ Module.IsPrincipal R M₂ where mp
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
If the numerator ideal of a fractional ideal is principal, then so is the fracti
onal ideal.
-/
theorem isPrincipal_of_isPrincipal_num [IsDomain R]
    (I : FractionalIdeal R⁰ (FractionRing R)) (hI : I.num.IsPrincipal) :
    (I : Submodule R (FractionRing R)).IsPrincipal :=
  Module.isPrincipal_submodule_iff.mp
    <| (FractionalIdeal.equivNumOfIsLocalization I).isPrincipal_iff.mpr
    <| Module.isPrincipal_submodule_iff.mpr hI

end PrincipalIdeal

variable {R₁ : Type*} [CommRing R₁]
variable {K : Type*} [Field K] [Algebra R₁ K]

/-
**FractionalIdeal.isNoetherian_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：isNoetherian_zero : IsNoetherian R₁ (0 : FractionalIdeal R₁⁰ K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isNoetherian_submodule`：isNoetherian_submodule {N : Submodule R M} : IsN
oetherian R N ↔ forall s : Submodule R M, s <= N -> s.FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
-/
theorem isNoetherian_zero : IsNoetherian R₁ (0 : FractionalIdeal R₁⁰ K) :=
  isNoetherian_submodule.mpr fun I (hI : I ≤ (0 : FractionalIdeal R₁⁰ K)) => by
    rw [coe_zero, le_bot_iff] at hI
    rw [hI]
    exact fg_bot
/-
**FractionalIdeal.isNoetherian_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：isNoetherian_iff {I : FractionalIdeal R₁⁰ K} : IsNoetherian R₁ I ↔ forall 
J <= I, (J : Submodule R₁ K).FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isNoetherian_submodule`：isNoetherian_submodule {N : Submodule R M} : IsN
oetherian R N ↔ forall s : Submodule R M, s <= N -> s.FG
· 使用定理 `FractionalIdeal.isFractional_of_le`：isFractional_of_le {I : Submodule R 
P} {J : FractionalIdeal S P} (hIJ : I <= J) : IsFractional S I
-/
theorem isNoetherian_iff {I : FractionalIdeal R₁⁰ K} :
    IsNoetherian R₁ I ↔ ∀ J ≤ I, (J : Submodule R₁ K).FG :=
  isNoetherian_submodule.trans ⟨fun h _ hJ => h _ hJ, fun h J hJ => h ⟨J, isFractional_of_le hJ⟩ hJ⟩
/-
**FractionalIdeal.isNoetherian_coeIdeal** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：isNoetherian_coeIdeal [IsNoetherianRing R₁] (I : Ideal R₁) : IsNoetherian 
R₁ (I : FractionalIdeal R₁⁰ K)
参数：I : Ideal R₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.isNoetherian_iff`：isNoetherian_iff {I : FractionalIdeal 
R₁⁰ K} : IsNoetherian R₁ I ↔ forall J <= I, (J : Submodule R₁ K).FG
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.le_one_iff_exists_coeIdeal`：le_one_iff_exists_coeIdeal {
J : FractionalIdeal S P} : J <= (1 : FractionalIdeal S P) ↔ exists I : Ideal R, 
↑I = J
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `FractionalIdeal.coeIdeal_le_one`：coeIdeal_le_one {I : Ideal R} : (I : Fr
actionalIdeal S P) <= 1
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
-/
theorem isNoetherian_coeIdeal [IsNoetherianRing R₁] (I : Ideal R₁) :
    IsNoetherian R₁ (I : FractionalIdeal R₁⁰ K) := by
  rw [isNoetherian_iff]
  intro J hJ
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp (le_trans hJ coeIdeal_le_one)
  exact (IsNoetherian.noetherian J).map _

variable [IsFractionRing R₁ K] [IsDomain R₁]
/-
**FractionalIdeal.isNoetherian_spanSingleton_inv_to_map_mul** 是 Mathlib 中的一个定理，位
于命名空间 `FractionalIdeal`。
形式化陈述：isNoetherian_spanSingleton_inv_to_map_mul (x : R₁) {I : FractionalIdeal R₁
⁰ K} (hI : IsNoetherian R₁ I) : IsNoetherian R₁ (spanSingleton R₁⁰ (algebraMap R
₁ K x)⁻¹ * I : FractionalIdeal R₁⁰ K)
参数：x : R₁；hI : IsNoetherian R₁ I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `FractionalIdeal.spanSingleton_zero`：spanSingleton_zero : spanSingleton S
 (0 : P) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `FractionalIdeal.isNoetherian_zero`：isNoetherian_zero : IsNoetherian R₁ (
0 : FractionalIdeal R₁⁰ K)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.spanSingleton_ne_zero_iff`：spanSingleton_ne_zero_iff {y 
: P} : spanSingleton S y != 0 ↔ y != 0
· 使用定理 `FractionalIdeal.isNoetherian_iff`：isNoetherian_iff {I : FractionalIdeal 
R₁⁰ K} : IsNoetherian R₁ I ↔ forall J <= I, (J : Submodule R₁ K).FG
· 使用定理 `FractionalIdeal.le_div_iff_mul_le`：le_div_iff_mul_le {I J J' : Fractiona
lIdeal R₁⁰ K} (hJ' : J' != 0) : I <= J / J' ↔ I * J' <= J
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.div_spanSingleton`：div_spanSingleton (J : FractionalIdea
l R₁⁰ K) (d : K) : J / spanSingleton R₁⁰ d = spanSingleton R₁⁰ d⁻¹ * J
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `FractionalIdeal.coe_spanSingleton`：coe_spanSingleton (x : P) : (spanSing
leton S x : Submodule R P) = span R {x}
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `FractionalIdeal.spanSingleton_mul_spanSingleton`：spanSingleton_mul_spanS
ingleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x 
* y)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem isNoetherian_spanSingleton_inv_to_map_mul (x : R₁) {I : FractionalIdeal R₁⁰ K}
    (hI : IsNoetherian R₁ I) :
    IsNoetherian R₁ (spanSingleton R₁⁰ (algebraMap R₁ K x)⁻¹ * I : FractionalIdeal R₁⁰ K) := by
  classical
  by_cases hx : x = 0
  · rw [hx, map_zero, inv_zero, spanSingleton_zero, zero_mul]
    exact isNoetherian_zero
  have h_gx : algebraMap R₁ K x ≠ 0 :=
    mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).mp (IsFractionRing.injective _ _) x) hx
  have h_spanx : spanSingleton R₁⁰ (algebraMap R₁ K x) ≠ 0 := spanSingleton_ne_zero_iff.mpr h_gx
  rw [isNoetherian_iff] at hI ⊢
  intro J hJ
  rw [← div_spanSingleton, le_div_iff_mul_le h_spanx] at hJ
  obtain ⟨s, hs⟩ := hI _ hJ
  use s * {(algebraMap R₁ K x)⁻¹}
  rw [Finset.coe_mul, Finset.coe_singleton, ← span_mul_span, hs, ← coe_spanSingleton R₁⁰, ←
    coe_mul, mul_assoc, spanSingleton_mul_spanSingleton, mul_inv_cancel₀ h_gx, spanSingleton_one,
    mul_one]

/-- Every fractional ideal of a Noetherian integral domain is Noetherian. -/
/-
**FractionalIdeal.isNoetherian** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：isNoetherian [IsNoetherianRing R₁] (I : FractionalIdeal R₁⁰ K) : IsNoether
ian R₁ I
参数：I : FractionalIdeal R₁⁰ K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.exists_eq_spanSingleton_mul`：exists_eq_spanSingleton_mul
 (I : FractionalIdeal R₁⁰ K) : exists (a : R₁) (aI : Ideal R₁), a != 0 ∧ I = spa
nSingleton R₁⁰ (algebraMap R₁ K a…
· 使用定理 `FractionalIdeal.isNoetherian_spanSingleton_inv_to_map_mul`：isNoetherian_
spanSingleton_inv_to_map_mul (x : R₁) {I : FractionalIdeal R₁⁰ K} (hI : IsNoethe
rian R₁ I) : IsNoetherian R₁ (spanSingleton R₁⁰…
· 使用定理 `FractionalIdeal.isNoetherian_coeIdeal`：isNoetherian_coeIdeal [IsNoetheri
anRing R₁] (I : Ideal R₁) : IsNoetherian R₁ (I : FractionalIdeal R₁⁰ K)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Every fractional ideal of a Noetherian integral domain is Noetherian.
-/
theorem isNoetherian [IsNoetherianRing R₁] (I : FractionalIdeal R₁⁰ K) : IsNoetherian R₁ I := by
  obtain ⟨d, J, _, rfl⟩ := exists_eq_spanSingleton_mul I
  apply isNoetherian_spanSingleton_inv_to_map_mul
  apply isNoetherian_coeIdeal

section Adjoin

variable (S)
variable [IsLocalization S P] (x : P)

/-- `A[x]` is a fractional ideal for every integral `x`. -/
/-
**FractionalIdeal.isFractional_adjoin_integral** 是 Mathlib 中的一个定理，位于命名空间 `Fracti
onalIdeal`。
形式化陈述：isFractional_adjoin_integral (hx : IsIntegral R x) : IsFractional S (Subal
gebra.toSubmodule (Algebra.adjoin R ({x} : Set P)))
参数：hx : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional_of_fg`：isFractional_of_fg [IsLocalization S
 P] {I : Submodule R P} (hI : I.FG) : IsFractional S I
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG

--- 原说明 ---
`A[x]` is a fractional ideal for every integral `x`.
-/
theorem isFractional_adjoin_integral (hx : IsIntegral R x) :
    IsFractional S (Subalgebra.toSubmodule (Algebra.adjoin R ({x} : Set P))) :=
  isFractional_of_fg hx.fg_adjoin_singleton

/-- `FractionalIdeal.adjoinIntegral (S : Submonoid R) x hx` is `R[x]` as a fractional ideal,
where `hx` is a proof that `x : P` is integral over `R`. -/
-- Porting note: `@[simps]` generated a `Subtype.val` coercion instead of a
-- `FractionalIdeal.coeToSubmodule` coercion
/-
**FractionalIdeal.adjoinIntegral** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：adjoinIntegral (hx : IsIntegral R x) : FractionalIdeal S P
参数：hx : IsIntegral R x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional_adjoin_integral`：isFractional_adjoin_integr
al (hx : IsIntegral R x) : IsFractional S (Subalgebra.toSubmodule (Algebra.adjoi
n R ({x} : Set P)))
-/
def adjoinIntegral (hx : IsIntegral R x) : FractionalIdeal S P :=
  ⟨_, isFractional_adjoin_integral S x hx⟩

@[simp]
/-
**FractionalIdeal.adjoinIntegral_coe** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：adjoinIntegral_coe (hx : IsIntegral R x) : (adjoinIntegral S x hx : Submod
ule R P) = (Subalgebra.toSubmodule (Algebra.adjoin R ({x} : Set P)))
参数：hx : IsIntegral R x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjoinIntegral_coe (hx : IsIntegral R x) :
    (adjoinIntegral S x hx : Submodule R P) =
      (Subalgebra.toSubmodule (Algebra.adjoin R ({x} : Set P))) :=
  rfl
/-
**FractionalIdeal.mem_adjoinIntegral_self** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
形式化陈述：mem_adjoinIntegral_self (hx : IsIntegral R x) : x in adjoinIntegral S x hx
参数：hx : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem mem_adjoinIntegral_self (hx : IsIntegral R x) : x ∈ adjoinIntegral S x hx :=
  Algebra.subset_adjoin (Set.mem_singleton x)

end Adjoin

section RingEquiv

open IsFractionRing

variable {R S : Type*} (K L : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [CommRing K] [CommRing L] [Algebra R K] [Algebra S L] [IsFractionRing R K] [IsFractionRing S L]
  (f : R ≃+* S)

local instance (f : R ≃+* S) : RingHomInvPair (f : R →+* S) f.symm :=
  RingHomInvPair.of_ringEquiv f

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Submodule R K` is fractional with respect to
`R⁰`, then `I.map (IsFractionRing.semilinearEquivOfRingEquiv K L f).toLinearMap`
is fractional with respect to `S⁰`.

Do not confuse with `IsFractional.map`. -/
/-
**FractionalIdeal._root_.IsFractional.mapEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Fracti
onalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : R ≃+* S` is a ring isomorphism and `I : Submodule R K` is fractional wit
h respect to
`R⁰`, then `I.map (IsFractionRing.semilinearEquivOfRingEquiv K L f).toLinearMap`
is fractional with respect to `S⁰`.

Do not confuse with `IsFractional.map`.
-/
theorem _root_.IsFractional.mapEquiv {I : Submodule R K} (hI : IsFractional R⁰ I) :
    IsFractional S⁰ (I.map (semilinearEquivOfRingEquiv K L f).toLinearMap) := by
  simp only [IsFractional, mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submodule.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hI ⊢
  obtain ⟨r, hr0, hr⟩ := hI
  use f r
  refine ⟨by simp [hr0], ?_⟩
  intro x hx
  specialize hr x hx
  simp only [IsLocalization.IsInteger, RingHom.mem_rangeS] at hr ⊢
  obtain ⟨r', hr'⟩ := hr
  use f r'
  simp only [semilinearEquivOfRingEquiv, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe, Equiv.invFun_as_coe, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Algebra.smul_def, ← ringEquivOfRingEquiv_algebraMap f (K := K) (L := L) r,
    ← map_mul, ← Algebra.smul_def, ← hr', ringEquivOfRingEquiv_algebraMap]

set_option backward.isDefEq.respectTransparency.types false in
/-- The equiv `FractionalIdeal R⁰ K ≃+* FractionalIdeal S⁰ L`
  induced by a ring isomorphism `f : R ≃+* S`. -/
@[simps -isSimp]
/-
**FractionalIdeal.ringEquivOfRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdea
l`。
形式化陈述：ringEquivOfRingEquiv : FractionalIdeal R⁰ K ≃+* FractionalIdeal S⁰ L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.instRingHomInvPairToRingHomRingEquivSymm`：∀ {A : Type u_8
} {B : Type u_9} [inst : CommRing A] [inst_1 : CommRing B] (f : A ≃+* B), RingHo
mInvPair ↑f ↑f.symm

--- 原说明 ---
The equiv `FractionalIdeal R⁰ K ≃+* FractionalIdeal S⁰ L`
  induced by a ring isomorphism `f : R ≃+* S`.
-/
noncomputable def ringEquivOfRingEquiv :
    FractionalIdeal R⁰ K ≃+* FractionalIdeal S⁰ L :=
  { toFun I := ⟨Submodule.map (semilinearEquivOfRingEquiv _ _ f).toLinearMap I.val,
      IsFractional.mapEquiv K L f I.prop⟩
    invFun J := ⟨J.val.map (semilinearEquivOfRingEquiv _ _ f.symm).toLinearMap,
      IsFractional.mapEquiv L K f.symm J.prop⟩
    map_add' I J := by ext x; simp [← mem_coe]
    map_mul' I J := by
      simp only [FractionalIdeal.coe_ext_iff, val_eq_coe, coe_mul, coe_mk]
      apply le_antisymm <;> simp only [map_le_iff_le_comap, Submodule.mul_le, mem_coe, mem_comap,
          semilinearEquivOfRingEquiv_apply, map_mul, mem_map_equiv,
          semilinearEquivOfRingEquiv_symm_apply, LinearEquiv.coe_coe]
      · exact fun m hm n hn ↦ Submodule.mul_mem_mul (mem_map_of_mem hm) (mem_map_of_mem hn)
      · exact fun m hm n hn ↦ Submodule.mul_mem_mul hm hn
    left_inv I := by
      simp only [RingEquiv.symm_symm, val_eq_coe, ← Submodule.map_comp, LinearEquiv.comp_coe,
        coe_ext_iff, coe_mk]
      convert! Submodule.map_id _
      ext; simp [semilinearEquivOfRingEquiv, IsLocalization.map_map]
    right_inv I := by
      simp only [RingEquiv.symm_symm, val_eq_coe, ← Submodule.map_comp, LinearEquiv.comp_coe,
        coe_ext_iff, coe_mk]
      convert! Submodule.map_id _
      ext; simp [semilinearEquivOfRingEquiv, IsLocalization.map_map]}

set_option backward.isDefEq.respectTransparency.types false in
/-
**FractionalIdeal.ringEquivOfRingEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fraction
alIdeal`。
形式化陈述：ringEquivOfRingEquiv_apply (f : R ≃+* S) (I : FractionalIdeal (nonZeroDivi
sors R) K) : ringEquivOfRingEquiv K L f I = ⟨Submodule.map (semilinearEquivOfRin
gEquiv _ _ f).toLinearMap I.val, IsFractional.mapEquiv K L f I.prop⟩
参数：f : R ≃+* S；I : FractionalIdeal (nonZeroDivisors R) K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ringEquivOfRingEquiv_apply (f : R ≃+* S) (I : FractionalIdeal (nonZeroDivisors R) K) :
    ringEquivOfRingEquiv K L f I =
      ⟨Submodule.map (semilinearEquivOfRingEquiv _ _ f).toLinearMap I.val,
        IsFractional.mapEquiv K L f I.prop⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**FractionalIdeal.ringEquivOfRingEquiv_apply_val** 是 Mathlib 中的一个引理，位于命名空间 `Frac
tionalIdeal`。
形式化陈述：ringEquivOfRingEquiv_apply_val (f : R ≃+* S) (I : FractionalIdeal R⁰ K) : 
(ringEquivOfRingEquiv K L f I).val = I.val.map (semilinearEquivOfRingEquiv _ _ f
).toLinearMap
参数：f : R ≃+* S；I : FractionalIdeal R⁰ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ringEquivOfRingEquiv_apply_val (f : R ≃+* S) (I : FractionalIdeal R⁰ K) :
    (ringEquivOfRingEquiv K L f I).val =
      I.val.map (semilinearEquivOfRingEquiv _ _ f).toLinearMap  := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**FractionalIdeal.ringEquivOfRingEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `Fraction
alIdeal`。
形式化陈述：ringEquivOfRingEquiv_trans {T : Type*} [CommRing T] [IsDomain T] (M : Type
*) [CommRing M] [Algebra T M] [IsFractionRing T M] (f : R ≃+* S) (g : S ≃+* T) :
 ringEquivOfRingEquiv K M (f.trans g) = (ringEquivOfRingEquiv K L f).trans (ring
EquivOfRingEquiv L M g)
参数：M : Type*；f : R ≃+* S；g : S ≃+* T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsFractionRing.instRingHomInvPairToRingHomRingEquivSymm`：∀ {A : Type u_8
} {B : Type u_9} [inst : CommRing A] [inst_1 : CommRing B] (f : A ≃+* B), RingHo
mInvPair ↑f ↑f.symm
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHomSurjective.instToRingHomRingEquiv`：∀ {R₁ : Type u_1} {R₂ : Type u
_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] (σ : R₁ ≃+* R₂), RingHomSurjecti
ve ↑σ
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsFractionRing.semilinearEquivOfRingEquiv_comp`：semilinearEquivOfRingEqu
iv_comp {C : Type*} (M : Type*) [CommRing C] [CommRing M] [Algebra C M] [IsFract
ionRing C M] (g : B ≃+* C) : let : R…
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `RingEquiv.mk.congr_simp`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] 
[inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S]   (toEquiv toEquiv_1 : R ≃ S)
 (e_toEquiv :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ringEquivOfRingEquiv_trans {T : Type*} [CommRing T] [IsDomain T] (M : Type*) [CommRing M]
    [Algebra T M] [IsFractionRing T M] (f : R ≃+* S) (g : S ≃+* T) :
    ringEquivOfRingEquiv K M (f.trans g) =
      (ringEquivOfRingEquiv K L f).trans (ringEquivOfRingEquiv L M g) := by
  have : RingHomCompTriple f (g : S →+* T) (f.trans g : R →+* T) := ⟨rfl⟩
  ext1 I
  simp only [ringEquivOfRingEquiv, RingEquiv.coe_ringHom_trans, Function.comp_apply,
    semilinearEquivOfRingEquiv_comp K L f M, LinearEquiv.coe_trans,
    Submodule.map_comp, RingEquiv.coe_mk, Equiv.coe_fn_mk, RingEquiv.coe_trans]
/-
**FractionalIdeal.ringEquivOfRingEquiv_trans_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fr
actionalIdeal`。
形式化陈述：ringEquivOfRingEquiv_trans_apply {T : Type*} [CommRing T] [IsDomain T] (M 
: Type*) [CommRing M] [Algebra T M] [IsFractionRing T M] (f : R ≃+* S) (g : S ≃+
* T) (I : FractionalIdeal R⁰ K) : ringEquivOfRingEquiv K M (f.trans g) I = ringE
quivOfRingEquiv L M g (ringEquivOfRingEquiv K L f I)
参数：M : Type*；f : R ≃+* S；g : S ≃+* T；I : FractionalIdeal R⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.ringEquivOfRingEquiv_trans`：ringEquivOfRingEquiv_trans {
T : Type*} [CommRing T] [IsDomain T] (M : Type*) [CommRing M] [Algebra T M] [IsF
ractionRing T M] (f : R ≃+* S) (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ringEquivOfRingEquiv_trans_apply {T : Type*} [CommRing T] [IsDomain T] (M : Type*)
    [CommRing M] [Algebra T M] [IsFractionRing T M]
    (f : R ≃+* S) (g : S ≃+* T) (I : FractionalIdeal R⁰ K) :
    ringEquivOfRingEquiv K M (f.trans g) I =
      ringEquivOfRingEquiv L M g (ringEquivOfRingEquiv K L f I) := by
  simp [ringEquivOfRingEquiv_trans K L M]

set_option backward.isDefEq.respectTransparency.types false in
/-
**FractionalIdeal.ringEquivOfRingEquiv_refl** 是 Mathlib 中的一个引理，位于命名空间 `Fractiona
lIdeal`。
形式化陈述：ringEquivOfRingEquiv_refl : ringEquivOfRingEquiv K K (RingEquiv.refl R) = 
RingEquiv.refl (FractionalIdeal R⁰ K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `RingHomSurjective.instToRingHomRingEquiv`：∀ {R₁ : Type u_1} {R₂ : Type u
_2} [inst : Semiring R₁] [inst_1 : Semiring R₂] (σ : R₁ ≃+* R₂), RingHomSurjecti
ve ↑σ
· 使用定理 `IsFractionRing.instRingHomInvPairToRingHomRingEquivSymm`：∀ {A : Type u_8
} {B : Type u_9} [inst : CommRing A] [inst_1 : CommRing B] (f : A ≃+* B), RingHo
mInvPair ↑f ↑f.symm
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractional.mapEquiv`：∀ {R : Type u_5} {S : Type u_6} (K : Type u_7) (L
 : Type u_8) [inst : CommRing R] [IsDomain R] [inst_2 : CommRing S]   [IsDomain 
S] [inst_4 …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsFractionRing.ringEquivOfRingEquiv_refl`：ringEquivOfRingEquiv_refl : ri
ngEquivOfRingEquiv (.refl A) = .refl K
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ringEquivOfRingEquiv_refl :
    ringEquivOfRingEquiv K K (RingEquiv.refl R) = RingEquiv.refl (FractionalIdeal R⁰ K) := by
  ext I x
  simp only [ringEquivOfRingEquiv_apply, RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl,
    val_eq_coe, RingEquiv.refl_apply, ← mem_coe]
  simp [semilinearEquivOfRingEquiv]

set_option backward.isDefEq.respectTransparency.types false in
/-
**FractionalIdeal.ringEquivOfRingEquiv_spanSingleton** 是 Mathlib 中的一个引理，位于命名空间 `
FractionalIdeal`。
形式化陈述：ringEquivOfRingEquiv_spanSingleton (x : K) : FractionalIdeal.ringEquivOfRi
ngEquiv K L f (spanSingleton R⁰ x) = spanSingleton S⁰ (IsFractionRing.ringEquivO
fRingEquiv (L
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.instRingHomInvPairToRingHomRingEquivSymm`：∀ {A : Type u_8
} {B : Type u_9} [inst : CommRing A] [inst_1 : CommRing B] (f : A ≃+* B), RingHo
mInvPair ↑f ↑f.symm
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `FractionalIdeal.coe_spanSingleton`：coe_spanSingleton (x : P) : (spanSing
leton S x : Submodule R P) = span R {x}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `FractionalIdeal.spanSingleton.congr_simp`：∀ {R : Type u_5} [inst : CommR
ing R] (S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra 
R P]   [inst_3 : IsLocalizatio…
· 使用定理 `IsFractionRing.ringEquivOfRingEquiv_apply`：∀ {A : Type u_8} {K : Type u_
9} {B : Type u_10} {L : Type u_11} [inst : CommRing A] [inst_1 : CommRing B]   [
inst_2 : CommRing K] [inst_3 : …
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ringEquivOfRingEquiv_spanSingleton (x : K) :
    FractionalIdeal.ringEquivOfRingEquiv K L f (spanSingleton R⁰ x) =
      spanSingleton S⁰ (IsFractionRing.ringEquivOfRingEquiv (L := L) f x) := by
  simp only [ringEquivOfRingEquiv, val_eq_coe, RingEquiv.symm_symm, RingEquiv.coe_mk,
    Equiv.coe_fn_mk, coe_spanSingleton, IsFractionRing.ringEquivOfRingEquiv_apply]
  rw [SetLike.ext_iff]
  intro y
  simp only [← FractionalIdeal.mem_coe, coe_mk, mem_map_equiv, coe_spanSingleton,
    Submodule.mem_span_singleton, (semilinearEquivOfRingEquiv K L f).eq_symm_apply]
  constructor
  · rintro ⟨r, rfl⟩
    use f r
    exact .symm (map_smulₛₗ _ r x)
  · rintro ⟨s, rfl⟩
    use f.symm s
    simp only [Algebra.smul_def, semilinearEquivOfRingEquiv_apply, map_mul, map_eq, RingHom.coe_coe,
      IsFractionRing.ringEquivOfRingEquiv_apply, RingEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-
**FractionalIdeal.ringEquivOfRingEquiv_symm_eq** 是 Mathlib 中的一个引理，位于命名空间 `Fracti
onalIdeal`。
形式化陈述：ringEquivOfRingEquiv_symm_eq : (FractionalIdeal.ringEquivOfRingEquiv K L f
).symm = FractionalIdeal.ringEquivOfRingEquiv L K f.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.coe_nonUnitalRingHom_inj_iff`：coe_nonUnitalRingHom_inj_iff {R 
S : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f g : R 
≃+* S) : f = g ↔ (f : R ->ₙ+…
-/
lemma ringEquivOfRingEquiv_symm_eq :
    (FractionalIdeal.ringEquivOfRingEquiv K L f).symm =
      FractionalIdeal.ringEquivOfRingEquiv L K f.symm := by
  exact (RingEquiv.coe_nonUnitalRingHom_inj_iff (ringEquivOfRingEquiv K L f).symm
          (ringEquivOfRingEquiv L K f.symm)).mpr rfl

end RingEquiv

end FractionalIdeal

