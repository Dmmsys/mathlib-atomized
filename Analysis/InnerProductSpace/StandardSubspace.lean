/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Standard subspaces of a Hilbert space

This files defines standard subspaces of a complex Hilbert space: a standard subspace `S` of `H` is
a closed real subspace `S` such that `S ⊓ i S = ⊥` and `S ⊔ i S = ⊤`. For a standard subspace, one
can define a closable operator `x + i y ↦ x - i y` and develop an analogue of the Tomita-Takesaki
modular theory for von Neumann algebras. By considering inclusions of standard subspaces, one can
obtain unitary representations of various Lie groups.

## Main definitions and results

* `instance : InnerProductSpace ℝ H` for `InnerProductSpace ℂ H`, by restricting the scalar product
  to its real part

* `StandardSubspace` as a structure with a `ClosedSubmodule` for `InnerProductSpace ℝ H` satisfying
  `IsCyclic` and `IsSeparating`. Actually the interesting cases need `CompleteSpace H`, but the
  definition is given for a general case.

* `symplComp` as a `StandardSubspace` of the symplectic complement of a standard subspace with
  respect to `⟪⬝, ⬝⟫.im`

* `symplComp_symplComp_eq` the double symplectic complement is equal to itself

## References

* [Chap. 2 of Lecture notes by R. Longo](https://www.mat.uniroma2.it/longo/Lecture-Notes_files/LN-Part1.pdf)

* [Oberwolfach report](https://ems.press/content/serial-article-files/48171)

## TODO

Define the Tomita conjugation, prove Tomita's theorem, prove the KMS condition.
-/

@[expose] public section

open Complex ContinuousLinearMap
open scoped ComplexInnerProductSpace

section ScalarSMulCLE

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- the scalar product by a non-zero complex number as a continuous real-linear equivalence. -/
/-
**scalarSMulCLE** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：scalarSMulCLE (c : Complexˣ) : H ≃L[Real] H
参数：c : Complexˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the scalar product by a non-zero complex number as a continuous real-linear equi
valence.
-/
noncomputable def scalarSMulCLE (c : ℂˣ) : H ≃L[ℝ] H := ContinuousLinearEquiv.smulLeft c

@[simp]
/-
**scalarSMulCLE_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：scalarSMulCLE_apply (c : Complexˣ) (x : H) : scalarSMulCLE H c x = c • x
参数：c : Complexˣ；x : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma scalarSMulCLE_apply (c : ℂˣ) (x : H) : scalarSMulCLE H c x = c • x := rfl

@[simp]
/-
**scalarSMulCLE_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：scalarSMulCLE_symm_apply (c : Complexˣ) (x : H) : (scalarSMulCLE H c).symm
 x = c⁻¹ • x
参数：c : Complexˣ；x : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma scalarSMulCLE_symm_apply (c : ℂˣ) (x : H) : (scalarSMulCLE H c).symm x = c⁻¹ • x := rfl

end ScalarSMulCLE

namespace ClosedSubmodule

variable {H : Type*} [NormedAddCommGroup H] [ipc : InnerProductSpace ℂ H]

/-- `H` as a real Hilbert space. This instance is declared inside `ClosedSubmodule` namespace. If
one needs this structure (for example when considering standard subspaces), one should just `open
ClosedSubmodule` and not declare another instance. -/
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`H` as a real Hilbert space. This instance is declared inside `ClosedSubmodule` 
namespace. If
one needs this structure (for example when considering standard subspaces), one 
should just `open
ClosedSubmodule` and not declare another instance.
-/
noncomputable scoped instance : InnerProductSpace ℝ H where
  inner x y := ⟪x, y⟫.re
  norm_sq_eq_re_inner := by simp [RCLike.re_to_real, ipc.norm_sq_eq_re_inner]
  conj_inner_symm x y := by
    simp only [← ipc.conj_inner_symm x y, conj_trivial]
    rfl
  add_left := by simp
  smul_left := by simp
/-
**ClosedSubmodule.inner_real_eq_re_inner** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmod
ule`。
形式化陈述：inner_real_eq_re_inner (x y : H) : inner Real x y = ⟪x, y⟫.re
参数：x y : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inner_real_eq_re_inner (x y : H) : inner ℝ x y = ⟪x, y⟫.re := rfl

/-- The imaginary unit as an invertible element. -/
@[simps val]
/-
**ClosedSubmodule._root_.Complex.UnitI** 是 Mathlib 中的一个定义，位于命名空间 `ClosedSubmodul
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The imaginary unit as an invertible element.
-/
def _root_.Complex.UnitI : ℂˣ where
  val := I
  inv := -I
  val_inv := by simp
  inv_val := by simp

/-- The image of a closed submodule by the multiplication by `Complex.I`. -/
/-
**ClosedSubmodule.mulI** 是 Mathlib 中的一个缩写定义，位于命名空间 `ClosedSubmodule`。
形式化陈述：mulI (S : ClosedSubmodule Real H)
参数：S : ClosedSubmodule Real H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a closed submodule by the multiplication by `Complex.I`.
-/
noncomputable abbrev mulI (S : ClosedSubmodule ℝ H) := S.mapEquiv (scalarSMulCLE H UnitI)

/-- The symplectic complement of a closed submodule with respect to `⟪⬝, ⬝⟫.im`, defined as the
image of `mulI` and `orthogonal`. The proof that this is the symplectic complement is given by
`mem_symplComp_iff`. -/
/-
**ClosedSubmodule.symplComp** 是 Mathlib 中的一个缩写定义，位于命名空间 `ClosedSubmodule`。
形式化陈述：symplComp (S : ClosedSubmodule Real H)
参数：S : ClosedSubmodule Real H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symplectic complement of a closed submodule with respect to `⟪⬝, ⬝⟫.im`, def
ined as the
image of `mulI` and `orthogonal`. The proof that this is the symplectic compleme
nt is given by
`mem_symplComp_iff`.
-/
noncomputable abbrev symplComp (S : ClosedSubmodule ℝ H) := (S.mulI)ᗮ
/-
**ClosedSubmodule.mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mem_iff (S : ClosedSubmodule Real H) {x : H} : x in S ↔ x in S.toSubmodule
.carrier
参数：S : ClosedSubmodule Real H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.to_iff`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma mem_iff (S : ClosedSubmodule ℝ H) {x : H} : x ∈ S ↔ x ∈ S.toSubmodule.carrier := by
  exact Eq.to_iff rfl
/-
**ClosedSubmodule.mem_symplComp_iff** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mem_symplComp_iff {x : H} {S : ClosedSubmodule Real H} : x in S.symplComp 
↔ forall y in S, ⟪y, x⟫.im = 0
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
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Complex.val_UnitI`：↑Complex.UnitI = Complex.I
· 使用定理 `Complex.inv_I`：inv_I : I⁻¹ = -I
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `CStarModule.inner_op_smul_left`：inner_op_smul_left {a : A} {x y : E} : ⟪
a • x, y⟫ = ⟪x, y⟫ * star a
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `CStarModule.inner_neg_left`：∀ {A : Type u_1} {E : Type u_2} [inst : NonU
nitalRing A] [inst_1 : StarRing A] [inst_2 : AddCommGroup E]   [inst_3 : _root_.
Module ℂ A] [ins…
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma mem_symplComp_iff {x : H} {S : ClosedSubmodule ℝ H} :
    x ∈ S.symplComp ↔ ∀ y ∈ S, ⟪y, x⟫.im = 0 := by
  simp only [mem_orthogonal, mem_mapEquiv_iff, scalarSMulCLE_symm_apply, Units.smul_def,
    Units.val_inv_eq_inv_val, val_UnitI, inv_I, neg_smul]
  constructor
  · intro h y hy
    have hiy := h (I • y)
    simp only [← smul_assoc, smul_eq_mul, I_mul_I, neg_smul, one_smul, neg_neg] at hiy
    simpa [inner_real_eq_re_inner] using! hiy hy
  · intro h _ hy
    have hiy := h _ hy
    simpa [inner_smul_left] using! hiy
/-
**ClosedSubmodule.mulI_orthogonal_eq_symplComp** 是 Mathlib 中的一个引理，位于命名空间 `Closed
Submodule`。
形式化陈述：mulI_orthogonal_eq_symplComp (S : ClosedSubmodule Real H) : Sᗮ.mulI = S.sy
mplComp
参数：S : ClosedSubmodule Real H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ClosedSubmodule.mem_iff`：mem_iff (S : ClosedSubmodule Real H) {x : H} : 
x in S ↔ x in S.toSubmodule.carrier
· 使用引理 `ClosedSubmodule.mem_symplComp_iff`：mem_symplComp_iff {x : H} {S : Closed
Submodule Real H} : x in S.symplComp ↔ forall y in S, ⟪y, x⟫.im = 0
· 使用引理 `ClosedSubmodule.mem_mapEquiv_iff`：mem_mapEquiv_iff (x : N) : x in (s.map
Equiv f) ↔ f.symm x in s
· 使用引理 `scalarSMulCLE_symm_apply`：scalarSMulCLE_symm_apply (c : Complexˣ) (x : H
) : (scalarSMulCLE H c).symm x = c⁻¹ • x
· 使用定理 `Units.inv_val`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), self.inv * 
↑self = 1
· 使用定理 `Units.val_inv`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), ↑self * sel
f.inv = 1
· 使用定理 `Units.inv_mk`：inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁
· 使用引理 `Units.smul_mk_apply`：smul_mk_apply {M α : Type*} [Monoid M] [SMul M α] (
m n : M) (h₁) (h₂) (a : α) : (⟨m, n, h₁, h₂⟩ : Mˣ) • a = m • a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Complex.val_UnitI`：↑Complex.UnitI = Complex.I
· 使用定理 `Complex.inv_I`：inv_I : I⁻¹ = -I
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `CStarModule.inner_op_smul_right`：∀ {A : Type u_1} {E : Type u_2} {inst :
 NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst
_3 : AddCommGroup E} …
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulI_orthogonal_eq_symplComp (S : ClosedSubmodule ℝ H) : Sᗮ.mulI = S.symplComp := by
  ext x
  rw [← mem_iff, ← mem_iff, mem_symplComp_iff, mem_mapEquiv_iff, scalarSMulCLE_symm_apply,
    Units.inv_mk, Units.smul_mk_apply]
  simp [inner_real_eq_re_inner]
/-
**ClosedSubmodule.mulI_orthogonal** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mulI_orthogonal (S : ClosedSubmodule Real H) : Sᗮ.mulI = S.mulIᗮ
参数：S : ClosedSubmodule Real H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ClosedSubmodule.mulI_orthogonal_eq_symplComp`：mulI_orthogonal_eq_symplCo
mp (S : ClosedSubmodule Real H) : Sᗮ.mulI = S.symplComp
-/
lemma mulI_orthogonal (S : ClosedSubmodule ℝ H) : Sᗮ.mulI = S.mulIᗮ := by
  rw [mulI_orthogonal_eq_symplComp]

@[simp]
/-
**ClosedSubmodule.mulI_symplComp** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mulI_symplComp {S : ClosedSubmodule Real H} : S.symplComp.mulI = S.mulI.sy
mplComp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosedSubmodule.symplComp.eq_1`：∀ {H : Type u_1} [inst : NormedAddCommGr
oup H] [ipc : InnerProductSpace ℂ H] (S : ClosedSubmodule ℝ H),   S.symplComp = 
S.mulIᗮ
· 使用引理 `ClosedSubmodule.mulI_orthogonal_eq_symplComp`：mulI_orthogonal_eq_symplCo
mp (S : ClosedSubmodule Real H) : Sᗮ.mulI = S.symplComp
-/
lemma mulI_symplComp {S : ClosedSubmodule ℝ H} :
    S.symplComp.mulI = S.mulI.symplComp := by
  rw [symplComp, symplComp, mulI_orthogonal_eq_symplComp]

@[simp]
/-
**ClosedSubmodule.mulI_mulI_eq** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mulI_mulI_eq (S : ClosedSubmodule Real H) : S.mulI.mulI = S
参数：S : ClosedSubmodule Real H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Complex.val_UnitI`：↑Complex.UnitI = Complex.I
· 使用定理 `Complex.inv_I`：inv_I : I⁻¹ = -I
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.I_mul_I`：I_mul_I : I * I = -1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.forall_smul_mem_iff`：forall_smul_mem_iff {R M S : Type*} [Monoid
 R] [MulAction R M] [SetLike S M] [SMulMemClass S R M] {N : S} {x : M} : (forall
 a : R, a • x in …
· 使用定理 `ClosedSubmodule.instSMulMemClass`：∀ {R : Type u_2} {M : Type u_3} [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3
 : _root_.Module R M],…
· 使用引理 `ClosedSubmodule.mem_mapEquiv_iff`：mem_mapEquiv_iff (x : N) : x in (s.map
Equiv f) ↔ f.symm x in s
-/
lemma mulI_mulI_eq (S : ClosedSubmodule ℝ H) : S.mulI.mulI = S := by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe]
  constructor
  · intro h
    rw [mem_mapEquiv_iff (scalarSMulCLE H UnitI), ← SetLike.forall_smul_mem_iff] at h
    simpa [← smul_assoc, Units.smul_def] using (h (-1 : ℝ))
  · intro h
    rw [← SetLike.forall_smul_mem_iff] at h
    simpa [← smul_assoc, Units.smul_def] using (h (-1 : ℝ))
/-
**ClosedSubmodule.involutive_mulI** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：involutive_mulI : Function.Involutive (mulI : ClosedSubmodule Real H -> Cl
osedSubmodule Real H)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosedSubmodule.mulI_mulI_eq`：mulI_mulI_eq (S : ClosedSubmodule Real H) 
: S.mulI.mulI = S
-/
lemma involutive_mulI :
    Function.Involutive (mulI : ClosedSubmodule ℝ H → ClosedSubmodule ℝ H) := mulI_mulI_eq

@[simp]
/-
**ClosedSubmodule.symplComp_symplComp_eq** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmod
ule`。
形式化陈述：symplComp_symplComp_eq [CompleteSpace H] {S : ClosedSubmodule Real H} : S.
symplComp.symplComp = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ClosedSubmodule.mulI_symplComp`：mulI_symplComp {S : ClosedSubmodule Real
 H} : S.symplComp.mulI = S.mulI.symplComp
· 使用引理 `ClosedSubmodule.mulI_mulI_eq`：mulI_mulI_eq (S : ClosedSubmodule Real H) 
: S.mulI.mulI = S
· 使用定理 `ClosedSubmodule.orthogonal_orthogonal_eq`：orthogonal_orthogonal_eq (K : 
ClosedSubmodule 𝕜 E) [K.HasOrthogonalProjection] : (Kᗮ)ᗮ = K
· 使用定理 `Submodule.instHasOrthogonalProjectionOfCompleteSpace`：∀ {𝕜 : Type u_1} {
E : Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerP
roductSpace 𝕜 E]   (K : ClosedSubmodule 𝕜 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symplComp_symplComp_eq [CompleteSpace H] {S : ClosedSubmodule ℝ H} :
    S.symplComp.symplComp = S := by simp [symplComp]
/-
**ClosedSubmodule.mulI_sup** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mulI_sup (S T : ClosedSubmodule Real H) : (S ⊔ T).mulI = S.mulI ⊔ T.mulI
参数：S T : ClosedSubmodule Real H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosedSubmodule.mulI.eq_1`：∀ {H : Type u_1} [inst : NormedAddCommGroup H
] [ipc : InnerProductSpace ℂ H] (S : ClosedSubmodule ℝ H),   S.mulI = (ClosedSub
module.mapEquiv…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ClosedSubmodule.mapEquiv_sup_eq`：mapEquiv_sup_eq (f : M ≃L[R] N) {s t : 
ClosedSubmodule R M} : (s ⊔ t).mapEquiv f = s.mapEquiv f ⊔ t.mapEquiv f
-/
lemma mulI_sup (S T : ClosedSubmodule ℝ H) :
    (S ⊔ T).mulI = S.mulI ⊔ T.mulI := by
  rw [mulI, ← mapEquiv_sup_eq]
/-
**ClosedSubmodule.mulI_inf** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mulI_inf (S T : ClosedSubmodule Real H) : (S ⊓ T).mulI = S.mulI ⊓ T.mulI
参数：S T : ClosedSubmodule Real H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosedSubmodule.mulI.eq_1`：∀ {H : Type u_1} [inst : NormedAddCommGroup H
] [ipc : InnerProductSpace ℂ H] (S : ClosedSubmodule ℝ H),   S.mulI = (ClosedSub
module.mapEquiv…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ClosedSubmodule.mapEquiv_inf_eq`：mapEquiv_inf_eq (f : M ≃L[R] N) {s t : 
ClosedSubmodule R M} : (s ⊓ t).mapEquiv f = s.mapEquiv f ⊓ t.mapEquiv f
-/
lemma mulI_inf (S T : ClosedSubmodule ℝ H) :
    (S ⊓ T).mulI = S.mulI ⊓ T.mulI := by
  rw [mulI, ← mapEquiv_inf_eq]

@[simp]
/-
**ClosedSubmodule.symplComp_sup** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：symplComp_sup (S T : ClosedSubmodule Real H) : (S ⊔ T).symplComp = S.sympl
Comp ⊓ T.symplComp
参数：S T : ClosedSubmodule Real H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosedSubmodule.symplComp.eq_1`：∀ {H : Type u_1} [inst : NormedAddCommGr
oup H] [ipc : InnerProductSpace ℂ H] (S : ClosedSubmodule ℝ H),   S.symplComp = 
S.mulIᗮ
· 使用引理 `ClosedSubmodule.mulI_sup`：mulI_sup (S T : ClosedSubmodule Real H) : (S ⊔
 T).mulI = S.mulI ⊔ T.mulI
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ClosedSubmodule.inf_orthogonal`：inf_orthogonal (K₁ K₂ : ClosedSubmodule 
𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ
-/
lemma symplComp_sup (S T : ClosedSubmodule ℝ H) :
    (S ⊔ T).symplComp = S.symplComp ⊓ T.symplComp := by
  rw [symplComp, symplComp, symplComp, mulI_sup]
  exact Eq.symm (inf_orthogonal S.mulI T.mulI)

@[simp]
/-
**ClosedSubmodule.symplComp_inf** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：symplComp_inf [CompleteSpace H] (S T : ClosedSubmodule Real H) : (S ⊓ T).s
ymplComp = S.symplComp ⊔ T.symplComp
参数：S T : ClosedSubmodule Real H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosedSubmodule.symplComp.eq_1`：∀ {H : Type u_1} [inst : NormedAddCommGr
oup H] [ipc : InnerProductSpace ℂ H] (S : ClosedSubmodule ℝ H),   S.symplComp = 
S.mulIᗮ
· 使用引理 `ClosedSubmodule.mulI_inf`：mulI_inf (S T : ClosedSubmodule Real H) : (S ⊓
 T).mulI = S.mulI ⊓ T.mulI
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ClosedSubmodule.sup_orthogonal`：sup_orthogonal [CompleteSpace E] (K₁ K₂ 
: ClosedSubmodule 𝕜 E) : K₁ᗮ ⊔ K₂ᗮ = (K₁ ⊓ K₂)ᗮ
-/
lemma symplComp_inf [CompleteSpace H] (S T : ClosedSubmodule ℝ H) :
    (S ⊓ T).symplComp = S.symplComp ⊔ T.symplComp := by
  rw [symplComp, symplComp, symplComp, mulI_inf]
  exact Eq.symm (sup_orthogonal S.mulI T.mulI)

end ClosedSubmodule

section Def

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A standard subspace `S` of a complex Hilbert space (or just an inner product space) `H` is a
closed real subspace `S` such that `S ⊓ i S = ⊥` and `S ⊔ i S = ⊤`. -/
@[ext]
/-
**StandardSubspace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(H : Type u_1) → [inst : NormedAddCommGroup H] → [InnerProductSpace ℂ H] →
 Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A standard subspace `S` of a complex Hilbert space (or just an inner product spa
ce) `H` is a
closed real subspace `S` such that `S ⊓ i S = ⊥` and `S ⊔ i S = ⊤`.
-/
structure StandardSubspace where
  /-- A real closed subspace `S`. -/
  toClosedSubmodule : ClosedSubmodule ℝ H
  /-- `S` is separating, that is, `S ⊓ i S` is the trivial subspace. -/
  IsSeparating : toClosedSubmodule ⊓ toClosedSubmodule.mulI = ⊥
  /-- `S` is cyclic, that is, `S ⊔ i S` is the whole space. -/
  IsCyclic : toClosedSubmodule ⊔ toClosedSubmodule.mulI = ⊤

end Def

namespace StandardSubspace

open ClosedSubmodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp]
/-
**StandardSubspace.toClosedSubmodule_inj** 是 Mathlib 中的一个引理，位于命名空间 `StandardSubs
pace`。
形式化陈述：toClosedSubmodule_inj {S T : StandardSubspace H} : S.toClosedSubmodule = T
.toClosedSubmodule ↔ S = T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `StandardSubspace.ext_iff`：∀ {H : Type u_1} {inst : NormedAddCommGroup H}
 {inst_1 : InnerProductSpace ℂ H} {x y : StandardSubspace H},   x = y ↔ x.toClos
edSubmodule = …
-/
lemma toClosedSubmodule_inj {S T : StandardSubspace H} :
    S.toClosedSubmodule = T.toClosedSubmodule ↔ S = T :=
  StandardSubspace.ext_iff.symm
/-
**StandardSubspace.toClosedSubmodule_injective** 是 Mathlib 中的一个引理，位于命名空间 `Standa
rdSubspace`。
形式化陈述：toClosedSubmodule_injective : Function.Injective (toClosedSubmodule (H
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `StandardSubspace.toClosedSubmodule_inj`：toClosedSubmodule_inj {S T : Sta
ndardSubspace H} : S.toClosedSubmodule = T.toClosedSubmodule ↔ S = T
-/
lemma toClosedSubmodule_injective : Function.Injective (toClosedSubmodule (H := H)) :=
  fun _ _ ↦ toClosedSubmodule_inj.mp

/-- The image of a standard subspace by the multiplication by `Complex.I`, bundled as a
`StandardSubspace`. -/
/-
**StandardSubspace.mulI** 是 Mathlib 中的一个定义，位于命名空间 `StandardSubspace`。
形式化陈述：mulI (S : StandardSubspace H) : StandardSubspace H where toClosedSubmodule
参数：S : StandardSubspace H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a standard subspace by the multiplication by `Complex.I`, bundled a
s a
`StandardSubspace`.
-/
noncomputable def mulI (S : StandardSubspace H) : StandardSubspace H where
  toClosedSubmodule := S.toClosedSubmodule.mulI
  IsSeparating := by simpa [mulI_mulI_eq, inf_comm] using S.IsSeparating
  IsCyclic := by simpa [mulI_mulI_eq, sup_comm] using S.IsCyclic

/-- The symplectic complement of a standard subspace, bundled as a `StandardSubspace`. -/
/-
**StandardSubspace.symplComp** 是 Mathlib 中的一个定义，位于命名空间 `StandardSubspace`。
形式化陈述：symplComp [CompleteSpace H] (S : StandardSubspace H) : StandardSubspace H 
where toClosedSubmodule
参数：S : StandardSubspace H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symplectic complement of a standard subspace, bundled as a `StandardSubspace
`.
-/
noncomputable def symplComp [CompleteSpace H] (S : StandardSubspace H) : StandardSubspace H where
  toClosedSubmodule := S.toClosedSubmodule.symplComp
  IsSeparating := by
    simp [mulI_symplComp, ClosedSubmodule.inf_orthogonal, sup_comm, S.IsCyclic]
  IsCyclic := by
    simp [mulI_symplComp, ClosedSubmodule.sup_orthogonal, inf_comm, S.IsSeparating]

@[simp]
/-
**StandardSubspace.symplComp_symplComp_eq** 是 Mathlib 中的一个定理，位于命名空间 `StandardSub
space`。
形式化陈述：symplComp_symplComp_eq [CompleteSpace H] (S : StandardSubspace H) : S.symp
lComp.symplComp = S
参数：S : StandardSubspace H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `StandardSubspace.toClosedSubmodule_inj`：toClosedSubmodule_inj {S T : Sta
ndardSubspace H} : S.toClosedSubmodule = T.toClosedSubmodule ↔ S = T
· 使用引理 `ClosedSubmodule.symplComp_symplComp_eq`：symplComp_symplComp_eq [Complete
Space H] {S : ClosedSubmodule Real H} : S.symplComp.symplComp = S
-/
theorem symplComp_symplComp_eq [CompleteSpace H] (S : StandardSubspace H) :
    S.symplComp.symplComp = S := toClosedSubmodule_inj.mp ClosedSubmodule.symplComp_symplComp_eq
/-
**StandardSubspace.involutive_symplComp** 是 Mathlib 中的一个引理，位于命名空间 `StandardSubsp
ace`。
形式化陈述：involutive_symplComp [CompleteSpace H] : Function.Involutive (symplComp : 
StandardSubspace H -> StandardSubspace H)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StandardSubspace.symplComp_symplComp_eq`：symplComp_symplComp_eq [Complet
eSpace H] (S : StandardSubspace H) : S.symplComp.symplComp = S
-/
lemma involutive_symplComp [CompleteSpace H] :
    Function.Involutive (symplComp : StandardSubspace H → StandardSubspace H)
  := symplComp_symplComp_eq

end StandardSubspace

