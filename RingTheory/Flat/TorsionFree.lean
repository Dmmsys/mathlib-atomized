/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.IsPrincipal

/-!
# Relationships between flatness and torsionfreeness.

We show that flat implies torsion-free, and that they're the same
concept for rings satisfying a certain property, including Dedekind
domains and valuation rings.

## Main theorems

* `Module.Flat.isSMulRegular_of_nonZeroDivisors`: Scalar multiplication by a nonzerodivisor of `R`
  is injective on a flat `R`-module.
* `Module.Flat.torsion_eq_bot`: `Torsion R M = ⊥` if `M` is a flat `R`-module.
* `Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal`: if localizing `R`
  at the complement of any maximal ideal is a valuation ring then `Torsion R M = ⊥` iff `M` is a
  flat `R`-module.
-/

public section
-- TODO: Add definition and properties of Prüfer domains.
-- TODO: Use `IsTorsionFree`.

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open Submodule (IsPrincipal torsion)

open TensorProduct

namespace Module.Flat

section Semiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

open LinearMap in
/-- Scalar multiplication `m ↦ r • m` by a regular `r` is injective on a flat module. -/
/-
**Module.Flat.isSMulRegular_of_isRegular** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`
。
形式化陈述：isSMulRegular_of_isRegular {r : R} (hr : IsRegular r) [Flat R M] : IsSMulR
egular M r
参数：hr : IsRegular r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsSMulRegular.eq_1`：∀ {R : Type u_1} (M : Type u_3) [inst : SMul R M] (c
 : R), IsSMulRegular M c = Function.Injective fun x => c • x

--- 原说明 ---
Scalar multiplication `m ↦ r • m` by a regular `r` is injective on a flat module
.
-/
lemma isSMulRegular_of_isRegular {r : R} (hr : IsRegular r) [Flat R M] :
    IsSMulRegular M r := by
  -- `r ∈ R⁰` implies that `toSpanSingleton R R r`, i.e. `(r * ⬝) : R → R` is injective
  -- Flatness implies that corresponding map `R ⊗[R] M →ₗ[R] R ⊗[R] M` is injective
  have h := Flat.rTensor_preserves_injective_linearMap (M := M)
    (toSpanSingleton R R r) <| hr.right
  -- But precomposing and postcomposing with the isomorphism `M ≃ₗ[R] (R ⊗[R] M)`
  -- we get a map `M →ₗ[R] M` which is just `(r • ·)`.
  have h2 : (fun (x : M) ↦ r • x) = ((TensorProduct.lid R M) ∘ₗ
            (rTensor M (toSpanSingleton R R r)) ∘ₗ
            (TensorProduct.lid R M).symm) := by ext; simp
  -- Hence `(r • ·) : M → M` is also injective
  rw [IsSMulRegular, h2]
  simp [h, LinearEquiv.injective]
/-
**Module.Flat.isTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：isTorsionFree [Flat R M] : IsTorsionFree R M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.isSMulRegular_of_isRegular`：isSMulRegular_of_isRegular {r : 
R} (hr : IsRegular r) [Flat R M] : IsSMulRegular M r
-/
instance isTorsionFree [Flat R M] : IsTorsionFree R M :=
  ⟨fun _ hr ↦ isSMulRegular_of_isRegular hr⟩

end Semiring

section Ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open scoped nonZeroDivisors

open LinearMap in
/-- Scalar multiplication `m ↦ r • m` by a nonzerodivisor `r` is injective on a flat module. -/
/-
**Module.Flat.isSMulRegular_of_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 `Module
.Flat`。
形式化陈述：isSMulRegular_of_nonZeroDivisors {r : R} (hr : r in R⁰) [Flat R M] : IsSMu
lRegular M r
参数：hr : r in R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.isSMulRegular_of_isRegular`：isSMulRegular_of_isRegular {r : 
R} (hr : IsRegular r) [Flat R M] : IsSMulRegular M r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_nonZeroDivisors_iff_isRegular`：le_nonZeroDivisors_iff_isRegular {S : 
Submonoid R} : S <= R⁰ ↔ forall s : S, IsRegular (s : R)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Scalar multiplication `m ↦ r • m` by a nonzerodivisor `r` is injective on a flat
 module.
-/
lemma isSMulRegular_of_nonZeroDivisors {r : R} (hr : r ∈ R⁰) [Flat R M] : IsSMulRegular M r := by
  apply isSMulRegular_of_isRegular
  exact le_nonZeroDivisors_iff_isRegular.mp (le_refl R⁰) ⟨r, hr⟩

/-- Flat modules have no torsion. -/
/-
**Module.Flat.torsion_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：torsion_eq_bot [Flat R M] : torsion R M = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `Module.Flat.isSMulRegular_of_nonZeroDivisors`：isSMulRegular_of_nonZeroDi
visors {r : R} (hr : r in R⁰) [Flat R M] : IsSMulRegular M r
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
Flat modules have no torsion.
-/
theorem torsion_eq_bot [Flat R M] : torsion R M = ⊥ := by
  rw [eq_bot_iff]
  -- indeed the definition of torsion means "annihilated by a nonzerodivisor"
  rintro m ⟨⟨r, hr⟩, h⟩
  -- and we just showed that 0 is the only element with this property
  exact isSMulRegular_of_nonZeroDivisors hr (by simpa using h)

/-- If `R` is Bezout then an `R`-module is flat iff it has no torsion. -/
@[stacks 0539 "Generalized valuation ring to Bezout domain"]
/-
**Module.Flat.flat_iff_torsion_eq_bot_of_isBezout** 是 Mathlib 中的一个定理，位于命名空间 `Mod
ule.Flat`。
形式化陈述：flat_iff_torsion_eq_bot_of_isBezout [IsBezout R] [IsDomain R] : Flat R M ↔
 torsion R M = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.torsion_eq_bot`：torsion_eq_bot [Flat R M] : torsion R M = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Flat.iff_lift_lsmul_comp_subtype_injective`：iff_lift_lsmul_comp_s
ubtype_injective : Flat R M ↔ forall ⦃I : Ideal R⦄, I.FG -> Function.Injective (
TensorProduct.lift ((lsmul R M).comp I.…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsBezout.isPrincipal_of_FG`：∀ {R : Type u} {inst : Semiring R} [self : I
sBezout R] (I : Ideal R), I.FG → Submodule.IsPrincipal I
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero`：eq_bot_iff_generator
_eq_zero (S : Submodule R M) [S.IsPrincipal] : S = ⊥ ↔ generator S = 0
· 使用定理 `Function.Injective.of_comp_right`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Surjec
tive g → Function.Inje…
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearEquiv.coe_rTensor`：∀ {R : Type u_1} [inst : CommSemiring R] (M : T
ype u_7) {N : Type u_8} {P : Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : Ad
dCommMonoid N…
· 使用定理 `LinearMap.rTensor.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (M : Ty
pe u_7) {N : Type u_8} {P : Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : Add
CommMonoid N…
· 使用定理 `TensorProduct.lift_comp_map`：lift_comp_map (i : M₂ ->ₛₗ[σ₂₃] N₂ ->ₛₗ[σ₂₃
] P₃) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : (lift i).comp (map f g) = lift
 ((i.comp f).comp…
· 使用定理 `LinearMap.compl₂_id`：compl₂_id (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) : h.compl
₂ LinearMap.id = h
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.subtype_isoBaseOfIsPrincipal_eq_mul`：subtype_isoBaseOfIsPrincipal_
eq_mul {I : Ideal R} [hprinc : I.IsPrincipal] (h : I != ⊥) : Submodule.subtype I
 ∘ₗ ↑(Ideal.isoBaseOfIsPrincipa…
· 使用定理 `LinearMap.lift_lsmul_mul_eq_lsmul_lift_lsmul`：lift_lsmul_mul_eq_lsmul_li
ft_lsmul {r : R} : lift (lsmul R M ∘ₗ mul R R r) = lsmul R M r ∘ₗ lift (lsmul R 
M)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearMap.lsmul_injective`：lsmul_injective [IsTorsionFree R M] {x : R} (
hx : x != 0) : Function.Injective (lsmul R M x)
· 使用引理 `Submodule.isTorsionFree_iff_torsion_eq_bot`：isTorsionFree_iff_torsion_eq
_bot : IsTorsionFree R M ↔ torsion R M = ⊥
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `R` is Bezout then an `R`-module is flat iff it has no torsion.
-/
theorem flat_iff_torsion_eq_bot_of_isBezout [IsBezout R] [IsDomain R] :
    Flat R M ↔ torsion R M = ⊥ := by
  -- one way is true in general
  refine ⟨fun _ ↦ torsion_eq_bot, ?_⟩
  -- now assume R is a Bezout domain and M is a torsionfree R-module
  intro htors
  -- we need to show that if I is an ideal of R then the natural map I ⊗ M → M is injective
  rw [iff_lift_lsmul_comp_subtype_injective]
  rintro I hFG
  -- If I = 0 this is obvious because I ⊗ M is a subsingleton (i.e. has ≤1 element)
  obtain (rfl | h) := eq_or_ne I ⊥
  · rintro x y -
    apply Subsingleton.elim
  · -- If I ≠ 0 then I ≅ R because R is Bezout and I is finitely generated
    have hprinc : I.IsPrincipal := IsBezout.isPrincipal_of_FG I hFG
    have : IsPrincipal.generator I ≠ 0 := by
      rwa [ne_eq, ← IsPrincipal.eq_bot_iff_generator_eq_zero]
    apply Function.Injective.of_comp_right _
      (LinearEquiv.rTensor M (Ideal.isoBaseOfIsPrincipal h)).surjective
    rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp, LinearEquiv.coe_rTensor, rTensor,
      lift_comp_map, LinearMap.compl₂_id, LinearMap.comp_assoc,
      Ideal.subtype_isoBaseOfIsPrincipal_eq_mul, LinearMap.lift_lsmul_mul_eq_lsmul_lift_lsmul,
      LinearMap.coe_comp]
    rw [← Submodule.isTorsionFree_iff_torsion_eq_bot] at htors
    refine Function.Injective.comp (LinearMap.lsmul_injective this) ?_
    rw [← Equiv.injective_comp (TensorProduct.lid R M).symm.toEquiv]
    convert! Function.injective_id
    ext
    simp

/-- If every localization of `R` at a maximal ideal is a valuation ring then an `R`-module
is flat iff it has no torsion. -/
/-
**Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal** 
是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal [IsDomain 
R] (h : forall (P : Ideal R), [P.IsMaximal] -> ValuationRing (Localization P.pri
meCompl)) : Flat R M ↔ torsion R M = ⊥
参数：h : forall (P : Ideal R), [P.IsMaximal] -> ValuationRing (Localization P.prim
eCompl)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.Flat.torsion_eq_bot`：torsion_eq_bot [Flat R M] : torsion R M = ⊥
· 使用定理 `Module.flat_of_localized_maximal`：flat_of_localized_maximal (h : forall 
(P : Ideal R) [P.IsMaximal], Flat R (LocalizedModule P.primeCompl M)) : Flat R M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.flat_iff_of_isLocalization`：flat_iff_of_isLocalization : Flat S M
 ↔ Flat R M
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`：flat_iff_torsion_eq_bot
_of_isBezout [IsBezout R] [IsDomain R] : Flat R M ↔ torsion R M = ⊥
· 使用定理 `ValuationRing.instIsBezout`：∀ {R : Type u_1} [inst : CommRing R] [inst_1
 : IsDomain R] [ValuationRing R], IsBezout R
· 使用引理 `Submodule.isTorsionFree_iff_torsion_eq_bot`：isTorsionFree_iff_torsion_eq
_bot : IsTorsionFree R M ↔ torsion R M = ⊥
· 使用定理 `IsLocalizedModule.instIsTorsionFreeLocalizationLocalizedModuleOfIsDomain
`：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M] [IsDomain R]   (S : Submonoid R)…

--- 原说明 ---
If every localization of `R` at a maximal ideal is a valuation ring then an `R`-
module
is flat iff it has no torsion.
-/
theorem flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal [IsDomain R]
    (h : ∀ (P : Ideal R), [P.IsMaximal] → ValuationRing (Localization P.primeCompl)) :
    Flat R M ↔ torsion R M = ⊥ := by
  refine ⟨fun _ ↦ Flat.torsion_eq_bot, fun h ↦ ?_⟩
  apply flat_of_localized_maximal
  intro P hP
  rw [← Submodule.isTorsionFree_iff_torsion_eq_bot] at h
  rw [← flat_iff_of_isLocalization (Localization P.primeCompl) P.primeCompl,
    Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- If `R` is a Dedekind domain then an `R`-module is flat iff it has no torsion. -/
@[stacks 0AUW "(1)"]
/-
**Module.Flat._root_.IsDedekindDomain.flat_iff_torsion_eq_bot** 是 Mathlib 中的一个定理
，位于命名空间 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a Dedekind domain then an `R`-module is flat iff it has no torsion.
-/
theorem _root_.IsDedekindDomain.flat_iff_torsion_eq_bot [IsDedekindDomain R] :
    Flat R M ↔ torsion R M = ⊥ := by
  apply flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
  exact fun P ↦ inferInstance
/-
**Module.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDedekindDomain R] [IsTorsionFree R M] : Flat R M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

end Ring

end Module.Flat

