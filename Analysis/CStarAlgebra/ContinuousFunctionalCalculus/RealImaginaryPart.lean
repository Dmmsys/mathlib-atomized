/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! # Interactions of the continuous functional calculus with the real and imaginary part -/

public section

open Complex ComplexStarModule

variable {A : Type*} [TopologicalSpace A]

section NonUnital

variable [NonUnitalRing A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [StarModule ℂ A] [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_re_id (a : A) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (re · : ℂ → ℂ) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfcₙ_id' ℂ a, ← cfcₙ_star, ← cfcₙ_add .., ← cfcₙ_smul ..]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [Complex.re_eq_add_conj, ← smul_one_smul ℂ 2⁻¹]
  simp [div_eq_inv_mul]
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_im_id (a : A) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (im · : ℂ → ℂ) a = ℑ a := by
  suffices cfcₙ (fun z : ℂ ↦ re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfcₙ_add .., cfcₙ_const_mul .., cfcₙ_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfcₙ_id' .., realPart_add_I_smul_imaginaryPart]
/-
**quasispectrum_realPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum_realPart (a : A) (ha : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_re_id`：cfcₙ_re_id (a : A) (ha : IsStarNormal a
· 使用引理 `cfcₙ_map_quasispectrum`：cfcₙ_map_quasispectrum : σₙ R (cfcₙ f a) = f '' 
σₙ R a
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quasispectrum_realPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℂ (ℜ a : A) = (fun x ↦ (re x : ℂ)) '' (quasispectrum ℂ a) := by
  rw [← cfcₙ_re_id a, cfcₙ_map_quasispectrum ..]

-- fails to find `IsScalarTower ℝ ℂ A`.
/-
**quasispectrum_realPart'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum_realPart' (a : A) (ha : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuasispectrumRestricts.image`：image (h : QuasispectrumRestricts a f) : f
 '' quasispectrum S a = quasispectrum R a
· 使用引理 `IsSelfAdjoint.quasispectrumRestricts`：IsSelfAdjoint.quasispectrumRestric
ts {a : A} (ha : IsSelfAdjoint a) : QuasispectrumRestricts a Complex.reCLM
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `quasispectrum_realPart`：quasispectrum_realPart (a : A) (ha : IsStarNorma
l a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quasispectrum_realPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℝ (ℜ a : A) = re '' (quasispectrum ℂ a) := by
  simp [← (ℜ a).2.quasispectrumRestricts.image, quasispectrum_realPart a, Set.image_image]
/-
**quasispectrum_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum_imaginaryPart (a : A) (ha : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_im_id`：cfcₙ_im_id (a : A) (ha : IsStarNormal a
· 使用引理 `cfcₙ_map_quasispectrum`：cfcₙ_map_quasispectrum : σₙ R (cfcₙ f a) = f '' 
σₙ R a
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quasispectrum_imaginaryPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℂ (ℑ a : A) = (fun x ↦ (im x : ℂ)) '' (quasispectrum ℂ a) := by
  rw [← cfcₙ_im_id a, cfcₙ_map_quasispectrum ..]

-- fails to find `IsScalarTower ℝ ℂ A`.
/-
**quasispectrum_imaginaryPart'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum_imaginaryPart' (a : A) (ha : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuasispectrumRestricts.image`：image (h : QuasispectrumRestricts a f) : f
 '' quasispectrum S a = quasispectrum R a
· 使用引理 `IsSelfAdjoint.quasispectrumRestricts`：IsSelfAdjoint.quasispectrumRestric
ts {a : A} (ha : IsSelfAdjoint a) : QuasispectrumRestricts a Complex.reCLM
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `quasispectrum_imaginaryPart`：quasispectrum_imaginaryPart (a : A) (ha : I
sStarNormal a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quasispectrum_imaginaryPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    quasispectrum ℝ (ℑ a : A) = im '' (quasispectrum ℂ a) := by
  simp [← (ℑ a).2.quasispectrumRestricts.image, quasispectrum_imaginaryPart a, Set.image_image]

variable [ContinuousMapZero.UniqueHom ℂ A]
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_realPart (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℂ (ℜ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ f (ℜ a : A) = cfcₙ (fun x ↦ f (re x)) a := by
  rw [quasispectrum_realPart a] at hf
  rw [← cfcₙ_re_id a, ← cfcₙ_comp' ..]
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_imaginaryPart (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℂ (ℑ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ f (ℑ a : A) = cfcₙ (fun x ↦ f (im x)) a := by
  rw [quasispectrum_imaginaryPart a] at hf
  rw [← cfcₙ_im_id a, ← cfcₙ_comp' ..]

variable [T2Space A]
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_comp_re (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℝ (ℜ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (fun x : ℂ ↦ f (re x)) a = cfcₙ f (ℜ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((re · : ℂ → ℂ) '' quasispectrum ℂ a) := by
    rw [quasispectrum_realPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfcₙ_real_eq_complex, ← cfcₙ_re_id a, ← cfcₙ_comp' ..]
    simp
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_comp_im (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (quasispectrum ℝ (ℑ a : A)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : IsStarNormal a := by cfc_tac) :
    cfcₙ (fun x : ℂ ↦ f (im x)) a = cfcₙ f (ℑ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((im · : ℂ → ℂ) '' quasispectrum ℂ a) := by
    rw [quasispectrum_imaginaryPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfcₙ_real_eq_complex, ← cfcₙ_im_id a, ← cfcₙ_comp' ..]
    simp

end NonUnital

section Unital

variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal]

/-
**cfc_re_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_re_id (a : A) (hp : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `realPart_apply_coe`：realPart_apply_coe (a : A) : (ℜ a : A) = (2 : Real)⁻
¹ • (a + star a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
· 使用引理 `cfc_star`：cfc_star (f : R -> R) (a : A) : cfc (fun x => star (f x)) a = 
star (cfc f a)
· 使用引理 `cfc_add`：cfc_add (f g : R -> R) (hf : ContinuousOn f (spectrum R a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `ContinuousOn.star`：ContinuousOn.star (hf : ContinuousOn f s) : Continuou
sOn (fun x => star (f x)) s
· 使用引理 `cfc_smul`：cfc_smul {S : Type*} [SMul S R] [ContinuousConstSMul S R] [SMu
lZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s : S) (f …
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ContinuousOn.fun_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `Complex.re_eq_add_conj`：re_eq_add_conj (z : Complex) : (z.re : Complex) 
= (z + conj z) / 2
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 35 条，此处仅展示前 30 条）
-/
lemma cfc_re_id (a : A) (hp : IsStarNormal a := by cfc_tac) :
    cfc (re · : ℂ → ℂ) a = ℜ a := by
  conv_rhs => rw [realPart_apply_coe, ← cfc_id' ℂ a, ← cfc_star, ← cfc_add .., ← cfc_smul ..]
  refine cfc_congr fun x hx ↦ ?_
  rw [Complex.re_eq_add_conj, ← smul_one_smul ℂ 2⁻¹]
  simp [div_eq_inv_mul]
/-
**cfc_im_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_im_id (a : A) (hp : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.re_add_im`：re_add_im (z : Complex) : (z.re : Complex) + z.im * I
 = z
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
· 使用定理 `realPart_add_I_smul_imaginaryPart`：realPart_add_I_smul_imaginaryPart (a 
: A) : (ℜ a : A) + I • (ℑ a : A) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `cfc_re_id`：cfc_re_id (a : A) (hp : IsStarNormal a
· 使用引理 `cfc_const_mul`：cfc_const_mul (r : R) (f : R -> R) (a : A) (hf : Continuo
usOn f (spectrum R a)
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
· 使用引理 `cfc_add`：cfc_add (f g : R -> R) (hf : ContinuousOn f (spectrum R a)
（共 35 条，此处仅展示前 30 条）
-/
lemma cfc_im_id (a : A) (hp : IsStarNormal a := by cfc_tac) :
    cfc (im · : ℂ → ℂ) a = ℑ a := by
  suffices cfc (fun z : ℂ ↦ re z + I * im z) a = ℜ a + I • ℑ a by
    rw [cfc_add .., cfc_const_mul .., cfc_re_id a] at this
    simpa
  simp [mul_comm I, re_add_im, cfc_id' .., realPart_add_I_smul_imaginaryPart]
/-
**spectrum_realPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：spectrum_realPart (a : A) (ha : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_re_id`：cfc_re_id (a : A) (hp : IsStarNormal a
· 使用引理 `cfc_map_spectrum`：cfc_map_spectrum (ha : p a
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
-/
lemma spectrum_realPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℂ (ℜ a : A) = (fun x ↦ (re x : ℂ)) '' (spectrum ℂ a) := by
  rw [← cfc_re_id a, cfc_map_spectrum ..]
/-
**spectrum_realPart'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：spectrum_realPart' (a : A) (ha : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `spectrum_realPart`：spectrum_realPart (a : A) (ha : IsStarNormal a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma spectrum_realPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℝ (ℜ a : A) = re '' (spectrum ℂ a) := by
  simp [← (ℜ a).2.spectrumRestricts.image, spectrum_realPart a, Set.image_image]
/-
**spectrum_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：spectrum_imaginaryPart (a : A) (ha : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_im_id`：cfc_im_id (a : A) (hp : IsStarNormal a
· 使用引理 `cfc_map_spectrum`：cfc_map_spectrum (ha : p a
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
lemma spectrum_imaginaryPart (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℂ (ℑ a : A) = (fun x ↦ (im x : ℂ)) '' (spectrum ℂ a) := by
  rw [← cfc_im_id a, cfc_map_spectrum ..]
/-
**spectrum_imaginaryPart'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：spectrum_imaginaryPart' (a : A) (ha : IsStarNormal a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `spectrum_imaginaryPart`：spectrum_imaginaryPart (a : A) (ha : IsStarNorma
l a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma spectrum_imaginaryPart' (a : A) (ha : IsStarNormal a := by cfc_tac) :
    spectrum ℝ (ℑ a : A) = im '' (spectrum ℂ a) := by
  simp [← (ℑ a).2.spectrumRestricts.image, spectrum_imaginaryPart a, Set.image_image]

variable [ContinuousMap.UniqueHom ℂ A]
/-
**cfc_realPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_realPart (f : Complex -> Complex) (a : A) (hf : ContinuousOn f (spectr
um Complex (ℜ a : A))
参数：f : Complex -> Complex；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_re_id`：cfc_re_id (a : A) (hp : IsStarNormal a
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用引理 `spectrum_realPart`：spectrum_realPart (a : A) (ha : IsStarNormal a
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
-/
lemma cfc_realPart (f : ℂ → ℂ) (a : A) (hf : ContinuousOn f (spectrum ℂ (ℜ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc f (ℜ a : A) = cfc (fun x ↦ f (re x)) a := by
  rw [spectrum_realPart a] at hf
  rw [← cfc_re_id a, ← cfc_comp' ..]
/-
**cfc_imaginaryPart** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_imaginaryPart (f : Complex -> Complex) (a : A) (hf : ContinuousOn f (s
pectrum Complex (ℑ a : A))
参数：f : Complex -> Complex；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_im_id`：cfc_im_id (a : A) (hp : IsStarNormal a
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用引理 `spectrum_imaginaryPart`：spectrum_imaginaryPart (a : A) (ha : IsStarNorma
l a
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
lemma cfc_imaginaryPart (f : ℂ → ℂ) (a : A)
    (hf : ContinuousOn f (spectrum ℂ (ℑ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc f (ℑ a : A) = cfc (fun x ↦ f (im x)) a := by
  rw [spectrum_imaginaryPart a] at hf
  rw [← cfc_im_id a, ← cfc_comp' ..]

variable [T2Space A]
/-
**cfc_comp_re** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp_re (f : Real -> Real) (a : A) (hf : ContinuousOn f (spectrum Real
 (ℜ a : A))
参数：f : Real -> Real；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `spectrum_realPart'`：spectrum_realPart' (a : A) (ha : IsStarNormal a
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `cfc_real_eq_complex`：cfc_real_eq_complex {a : A} (f : Real -> Real) (ha 
: IsSelfAdjoint a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_re_id`：cfc_re_id (a : A) (hp : IsStarNormal a
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
-/
lemma cfc_comp_re (f : ℝ → ℝ) (a : A)
    (hf : ContinuousOn f (spectrum ℝ (ℜ a : A)) := by cfc_tac)
    (ha : IsStarNormal a := by cfc_tac) :
    cfc (fun x : ℂ ↦ f (re x)) a = cfc f (ℜ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((re · : ℂ → ℂ) '' spectrum ℂ a) := by
    rw [spectrum_realPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfc_real_eq_complex, ← cfc_re_id a, ← cfc_comp' ..]
    simp
/-
**cfc_comp_im** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_comp_im (f : Real -> Real) (a : A) (hf : ContinuousOn f (spectrum Real
 (ℑ a : A))) (ha : IsStarNormal a
参数：f : Real -> Real；a : A；hf : ContinuousOn f (spectrum Real (ℑ a : A))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `spectrum_imaginaryPart'`：spectrum_imaginaryPart' (a : A) (ha : IsStarNor
mal a
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `cfc_real_eq_complex`：cfc_real_eq_complex {a : A} (f : Real -> Real) (ha 
: IsSelfAdjoint a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_im_id`：cfc_im_id (a : A) (hp : IsStarNormal a
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Complex.continuous_im`：Continuous Complex.im
-/
lemma cfc_comp_im (f : ℝ → ℝ) (a : A) (hf : ContinuousOn f (spectrum ℝ (ℑ a : A)))
    (ha : IsStarNormal a := by cfc_tac) :
    cfc (fun x : ℂ ↦ f (im x)) a = cfc f (ℑ a : A) := by
  have : ContinuousOn (fun x ↦ (f x.re) : ℂ → ℂ) ((im · : ℂ → ℂ) '' spectrum ℂ a) := by
    rw [spectrum_imaginaryPart' a] at hf
    refine continuous_ofReal.comp_continuousOn <| hf.comp (by fun_prop) ?_
    simpa [Set.mapsTo_image_iff, Function.comp_def] using Set.mapsTo_image ..
  conv_rhs =>
    rw [cfc_real_eq_complex, ← cfc_im_id a, ← cfc_comp' ..]
    simp

end Unital

