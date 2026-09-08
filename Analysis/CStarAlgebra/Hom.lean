/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Properties of C⋆-algebra homomorphisms

Here we collect properties of C⋆-algebra homomorphisms.

## Main declarations

+ `NonUnitalStarAlgHom.norm_map`: A non-unital star algebra monomorphism of complex C⋆-algebras
  is isometric.
-/

public section

open CStarAlgebra in
/-
**IsSelfAdjoint.map_spectrum_real** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.map_spectrum_real {F A B : Type*} [CStarAlgebra A] [CStarAlg
ebra B] [FunLike F A B] [AlgHomClass F Complex A B] [StarHomClass F A B] {a : A}
 (ha : IsSelfAdjoint a) (φ : F) (hφ : Function.Injective φ) : spectrum Real (φ a
) = spectrum Real a
参数：ha : IsSelfAdjoint a；φ : F；hφ : Function.Injective φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.spectrum_apply_subset`：spectrum_apply_subset (φ : F) (a : A) : σ 
((φ : A -> B) a) subseteq σ a
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `exists_continuous_zero_one_of_isClosed`：exists_continuous_zero_one_of_is
Closed [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : D
isjoint s t) : exists f : C(…
· 使用定理 `T4Space.toNormalSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self 
: T4Space X], NormalSpace X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `spectrum.isClosed`：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 𝕜
] [inst_1 : NormedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] (a : 
A), IsC…
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用引理 `StarAlgHomClass.map_cfc`：StarAlgHomClass.map_cfc (φ : F) (f : R -> R) (a
 : A) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `NonUnitalStarAlgHom.instContinuousLinearMapClassComplex`：instContinuousL
inearMapClassComplex : ContinuousLinearMapClass F Complex A B
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `IsSelfAdjoint.map`：map {F R S : Type*} [Star R] [Star S] [FunLike F R S]
 [StarHomClass F R S] {x : R} (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f 
x)
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
（共 46 条，此处仅展示前 30 条）
-/
lemma IsSelfAdjoint.map_spectrum_real {F A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]
    {a : A} (ha : IsSelfAdjoint a) (φ : F) (hφ : Function.Injective φ) :
    spectrum ℝ (φ a) = spectrum ℝ a := by
  have h_spec := AlgHom.spectrum_apply_subset ((φ : A →⋆ₐ[ℂ] B).restrictScalars ℝ) a
  refine Set.eq_of_subset_of_subset h_spec fun x hx ↦ ?_
  /- we prove the reverse inclusion by contradiction, so assume that `x ∈ spectrum ℝ a`, but
  `x ∉ spectrum ℝ (φ a)`. Then by Urysohn's lemma we can get a function for which `f x = 1`, but
  `f = 0` on `spectrum ℝ a`. -/
  by_contra hx'
  obtain ⟨f, h_eqOn, h_eqOn_x, -⟩ := exists_continuous_zero_one_of_isClosed
    (spectrum.isClosed (𝕜 := ℝ) (φ a)) (isClosed_singleton (x := x)) <| by simpa
  /- it suffices to show that `φ (f a) = 0`, for if so, then `f a = 0` by injectivity of `φ`, and
  hence `f = 0` on `spectrum ℝ a`, contradicting the fact that `f x = 1`. -/
  suffices φ (cfc f a) = 0 by
    rw [map_eq_zero_iff φ hφ, ← cfc_zero ℝ a, cfc_eq_cfc_iff_eqOn] at this
    exact zero_ne_one <| calc
      0 = f x := (this hx).symm
      _ = 1 := h_eqOn_x <| Set.mem_singleton x
  /- Finally, `φ (f a) = f (φ a) = 0`, where the last equality follows since `f = 0` on
  `spectrum ℝ (φ a)`. -/
  calc φ (cfc f a) = cfc f (φ a) := StarAlgHomClass.map_cfc φ f a
    _ = cfc (0 : ℝ → ℝ) (φ a) := cfc_congr h_eqOn
    _ = 0 := by simp

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

open CStarAlgebra Unitization in
/-- A non-unital star algebra monomorphism of complex C⋆-algebras is isometric. -/
/-
**NonUnitalStarAlgHom.norm_map** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：norm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖ = ‖a‖
参数：φ : F；hφ : Function.Injective φ；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `IsSelfAdjoint.star_mul_self`：star_mul_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (star x * x)
· 使用引理 `IsSelfAdjoint.toReal_spectralRadius_eq_norm`：IsSelfAdjoint.toReal_spectr
alRadius_eq_norm {a : A} (ha : IsSelfAdjoint a) : (spectralRadius Real a).toReal
 = ‖a‖
· 使用定理 `IsSelfAdjoint.map`：map {F R S : Type*} [Star R] [Star S] [FunLike F R S]
 [StarHomClass F R S] {x : R} (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f 
x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `IsSelfAdjoint.map_spectrum_real`：IsSelfAdjoint.map_spectrum_real {F A B 
: Type*} [CStarAlgebra A] [CStarAlgebra B] [FunLike F A B] [AlgHomClass F Comple
x A B] [StarHomClass …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Unitization.starMap_inr`：starMap_inr (φ : A ->⋆ₙₐ[R] B) (a : A) : starMa
p φ (inr a) = inr (φ a)
· 使用引理 `Unitization.norm_inr`：norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A non-unital star algebra monomorphism of complex C⋆-algebras is isometric.
-/
lemma norm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖ = ‖a‖ := by
  /- Since passing to the unitization is functorial, and it is an isometric embedding, we may assume
  that `φ` is a unital star algebra monomorphism and that `A` and `B` are unital C⋆-algebras. -/
  suffices ∀ {ψ : Unitization ℂ A →⋆ₐ[ℂ] Unitization ℂ B} (_ : Function.Injective ψ)
      (a : Unitization ℂ A), ‖ψ a‖ = ‖a‖ by
    simpa [norm_inr] using this (starMap_injective (φ := (φ : A →⋆ₙₐ[ℂ] B)) hφ) a
  intro ψ hψ a
  -- to show `‖ψ a‖ = ‖a‖`, by the C⋆-property it suffices to show `‖ψ (star a * a)‖ = ‖star a * a‖`
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp only [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
  /- since `star a * a` is selfadjoint, it has the same `ℝ`-spectrum as `ψ (star a * a)`.
  Since the spectral radius over `ℝ` coincides with the norm, `‖ψ (star a * a)‖ = ‖star a * a‖`. -/
  have ha : IsSelfAdjoint (star a * a) := .star_mul_self a
  calc ‖ψ (star a * a)‖ = (spectralRadius ℝ (ψ (star a * a))).toReal :=
      ha.map ψ |>.toReal_spectralRadius_eq_norm.symm
    _ = (spectralRadius ℝ (star a * a)).toReal := by
      simp only [spectralRadius, ha.map_spectrum_real ψ hψ]
    _ = ‖star a * a‖ := ha.toReal_spectralRadius_eq_norm

/-- A non-unital star algebra monomorphism of complex C⋆-algebras is isometric. -/
/-
**NonUnitalStarAlgHom.nnnorm_map** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalStarAlgHom`
。
形式化陈述：nnnorm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖₊ = ‖a‖₊
参数：φ : F；hφ : Function.Injective φ；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `NonUnitalStarAlgHom.norm_map`：norm_map (φ : F) (hφ : Function.Injective 
φ) (a : A) : ‖φ a‖ = ‖a‖

--- 原说明 ---
A non-unital star algebra monomorphism of complex C⋆-algebras is isometric.
-/
lemma nnnorm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_map φ hφ a
/-
**NonUnitalStarAlgHom.isometry** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalStarAlgHom`。
形式化陈述：isometry (φ : F) (hφ : Function.Injective φ) : Isometry φ
参数：φ : F；hφ : Function.Injective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用引理 `NonUnitalStarAlgHom.norm_map`：norm_map (φ : F) (hφ : Function.Injective 
φ) (a : A) : ‖φ a‖ = ‖a‖
-/
lemma isometry (φ : F) (hφ : Function.Injective φ) : Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ (norm_map φ hφ)

end NonUnitalStarAlgHom

