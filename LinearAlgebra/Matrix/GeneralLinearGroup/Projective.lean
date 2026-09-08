/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Edison Xie
-/
module

public import Mathlib.Data.Sign.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Projective general linear group

In this file we define `Matrix.ProjGenLinGroup n R` as the quotient of `GL n R` by its center.
We introduce notation `PGL(n, R)` for this group,
which works if `n` is either a finite type or a natural number.
If `n` is a number, then `PGL(n, R)` is interpreted as `PGL(Fin n, R)`.

## Main definitions

* `Matrix.SpecialLinearGroup.toPGL` is the natural map from `SL(n, R)` to `PGL(n, R)`.

* `Matrix.ProjectiveSpecialLinearGroup.toPGL` is the natural
  inclusion from `PSL(n, R)` to `PGL(n, R)`.

* `Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed` is an isomorphism between
  `PGL(n, F)` and `PSL(n, F)` in the case of an algebraically closed field.

-/

open scoped MatrixGroups

@[expose] public section

namespace Matrix

/-- Projective general linear group $PGL(n, R)$
defined as the quotient of the general linear group by its center. -/
/-
**Matrix.ProjGenLinGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：ProjGenLinGroup (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommR
ing R] : Type _
参数：n : Type*；R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projective general linear group $PGL(n, R)$
defined as the quotient of the general linear group by its center.
-/
def ProjGenLinGroup (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] : Type _ :=
  GL n R ⧸ Subgroup.center (GL n R)
  deriving Group

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup n R

@[inherit_doc]
scoped[MatrixGroups] notation "PGL(" n ", " R ")" => Matrix.ProjGenLinGroup (Fin n) R

namespace ProjGenLinGroup
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The natural projection from `GL n R` to `PGL n R`. -/
/-
**Matrix.ProjGenLinGroup.mk** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.ProjGenLinGroup`。
形式化陈述：mk : GL n R ->* PGL(n, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural projection from `GL n R` to `PGL n R`.
-/
def mk : GL n R →* PGL(n, R) := QuotientGroup.mk' (Subgroup.center (GL n R))
/-
**Matrix.ProjGenLinGroup.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.ProjGen
LinGroup`。
形式化陈述：mk_surjective : Function.Surjective (mk : GL n R -> PGL(n, R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
-/
theorem mk_surjective : Function.Surjective (mk : GL n R → PGL(n, R)) :=
  Quotient.mk_surjective
/-
**Matrix.ProjGenLinGroup.mk_eq_mk_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.ProjGen
LinGroup`。
形式化陈述：mk_eq_mk_iff' {g₁ g₂ : GL n R} : mk g₁ = mk g₂ ↔ exists z in Subgroup.cent
er (GL n R), g₁ * z = g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.mk'_eq_mk'`：∀ {G : Type u_1} [inst : Group G] (N : Subgrou
p G) [nN : N.Normal] {x y : G},   (QuotientGroup.mk' N) x = (QuotientGroup.mk' N
) y ↔ ∃ z ∈ N,…
-/
lemma mk_eq_mk_iff' {g₁ g₂ : GL n R} :
    mk g₁ = mk g₂ ↔ ∃ z ∈ Subgroup.center (GL n R), g₁ * z = g₂ :=
  QuotientGroup.mk'_eq_mk' (Subgroup.center (GL n R))
/-
**Matrix.ProjGenLinGroup.mk_eq_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.ProjGenL
inGroup`。
形式化陈述：mk_eq_mk_iff {g₁ g₂ : GL n R} : mk g₁ = mk g₂ ↔ exists u : Rˣ, g₁ * .scala
r n u = g₂
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
· 使用引理 `Matrix.GeneralLinearGroup.center_eq_range_scalar`：center_eq_range_scalar
 : Subgroup.center (GL n R) = (scalar n).range
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mk_eq_mk_iff {g₁ g₂ : GL n R} :
    mk g₁ = mk g₂ ↔ ∃ u : Rˣ, g₁ * .scalar n u = g₂ := by
  simp [mk_eq_mk_iff', Matrix.GeneralLinearGroup.center_eq_range_scalar]

@[simp]
/-
**Matrix.ProjGenLinGroup.ker_mk** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.ProjGenLinGrou
p`。
形式化陈述：ker_mk : mk.ker = Subgroup.center (GL n R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
-/
theorem ker_mk : mk.ker = Subgroup.center (GL n R) := QuotientGroup.ker_mk' _

@[simp]
/-
**Matrix.ProjGenLinGroup.mk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.ProjGenLinG
roup`。
形式化陈述：mk_eq_one {g : GL n R} : mk g = 1 ↔ g in Subgroup.center (GL n R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `Matrix.ProjGenLinGroup.ker_mk`：ker_mk : mk.ker = Subgroup.center (GL n R
)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_one {g : GL n R} : mk g = 1 ↔ g ∈ Subgroup.center (GL n R) := by
  rw [← MonoidHom.mem_ker, ker_mk]

@[simp]
/-
**Matrix.ProjGenLinGroup.mk_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.ProjGenLinGrou
p`。
形式化陈述：mk_one : mk (1 : GL n R) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_one : mk (1 : GL n R) = 1 := rfl

@[simp]
/-
**Matrix.ProjGenLinGroup.mk_scalar** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.ProjGenLinG
roup`。
形式化陈述：mk_scalar (u : Rˣ) : mk (.scalar n u) = 1
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `Matrix.ProjGenLinGroup.ker_mk`：ker_mk : mk.ker = Subgroup.center (GL n R
)
· 使用引理 `Matrix.GeneralLinearGroup.center_eq_range_scalar`：center_eq_range_scalar
 : Subgroup.center (GL n R) = (scalar n).range
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem mk_scalar (u : Rˣ) : mk (.scalar n u) = 1 := by
  rw [← MonoidHom.mem_ker, ker_mk, GeneralLinearGroup.center_eq_range_scalar]
  simp

@[elab_as_elim, cases_eliminator]
/-
**Matrix.ProjGenLinGroup.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.ProjGenL
inGroup`。
形式化陈述：induction_on {motive : PGL(n, R) -> Prop} (g : PGL(n, R)) (mk : forall g :
 GL n R, motive (ProjGenLinGroup.mk g)) : motive g
参数：n, R；g : PGL(n, R)；mk : forall g : GL n R, motive (ProjGenLinGroup.mk g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
theorem induction_on {motive : PGL(n, R) → Prop} (g : PGL(n, R))
    (mk : ∀ g : GL n R, motive (ProjGenLinGroup.mk g)) : motive g :=
  Quotient.inductionOn g mk

end ProjGenLinGroup

section isoPSL

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

open Matrix.ProjGenLinGroup

namespace SpecialLinearGroup

/-- The natural map from `SL(n, R)` to `PGL(n, R)` by composing the maps from `SL` to `GL` and the
  quotient map from `GL` to `PGL`. -/
/-
**Matrix.SpecialLinearGroup.toPGL** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix.SpecialLin
earGroup`。
形式化陈述：toPGL : SpecialLinearGroup n R ->* PGL(n, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map from `SL(n, R)` to `PGL(n, R)` by composing the maps from `SL` t
o `GL` and the
  quotient map from `GL` to `PGL`.
-/
abbrev toPGL : SpecialLinearGroup n R →* PGL(n, R) := mk.comp toGL
/-
**Matrix.SpecialLinearGroup.toPGL_ker** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.SpecialL
inearGroup`。
形式化陈述：toPGL_ker : toPGL.ker = Subgroup.center (SpecialLinearGroup n R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toPGL_ker : toPGL.ker = Subgroup.center (SpecialLinearGroup n R) := by
  ext; simp [toGL_mem_center_iff]

end SpecialLinearGroup

namespace ProjectiveSpecialLinearGroup

open Matrix.SpecialLinearGroup

/-- The natural inclusion map from `PSL(n, R)` to `PGL(n, R)` induced by the inclusion
  map from `SL(n, R)` to `GL(n, R)`. -/
/-
**Matrix.ProjectiveSpecialLinearGroup.toPGL** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Pr
ojectiveSpecialLinearGroup`。
形式化陈述：toPGL : ProjectiveSpecialLinearGroup n R ->* PGL(n, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion map from `PSL(n, R)` to `PGL(n, R)` induced by the inclusi
on
  map from `SL(n, R)` to `GL(n, R)`.
-/
def toPGL : ProjectiveSpecialLinearGroup n R →* PGL(n, R) :=
  QuotientGroup.lift _ SpecialLinearGroup.toPGL <| le_of_eq toPGL_ker.symm

@[simp]
/-
**Matrix.ProjectiveSpecialLinearGroup.toPGL_mk** 是 Mathlib 中的一个引理，位于命名空间 `Matrix
.ProjectiveSpecialLinearGroup`。
形式化陈述：toPGL_mk (g : SpecialLinearGroup n R) : ProjectiveSpecialLinearGroup.toPGL
 g = mk (toGL g)
参数：g : SpecialLinearGroup n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPGL_mk (g : SpecialLinearGroup n R) :
    ProjectiveSpecialLinearGroup.toPGL g = mk (toGL g) := rfl
/-
**Matrix.ProjectiveSpecialLinearGroup.toPGL_injective** 是 Mathlib 中的一个引理，位于命名空间 
`Matrix.ProjectiveSpecialLinearGroup`。
形式化陈述：toPGL_injective : Function.Injective (ProjectiveSpecialLinearGroup.toPGL (
n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `QuotientGroup.injective_lift_iff`：injective_lift_iff (φ : G ->* M) (HN :
 N <= φ.ker) : Function.Injective (QuotientGroup.lift N φ HN) ↔ N = φ.ker
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.SpecialLinearGroup.toPGL_ker`：toPGL_ker : toPGL.ker = Subgroup.ce
nter (SpecialLinearGroup n R)
-/
lemma toPGL_injective :
    Function.Injective (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)) :=
  QuotientGroup.injective_lift_iff _ _ _ |>.2 toPGL_ker.symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots** 是 Mathlib 中的一个引理，位于命
名空间 `Matrix.ProjectiveSpecialLinearGroup`。
形式化陈述：toPGL_surj_of_roots (hR : forall r : Rˣ, exists k : Rˣ, k ^ Fintype.card n
 = r) : Function.Surjective (ProjectiveSpecialLinearGroup.toPGL (n
参数：hR : forall r : Rˣ, exists k : Rˣ, k ^ Fintype.card n = r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ProjGenLinGroup.induction_on`：induction_on {motive : PGL(n, R) ->
 Prop} (g : PGL(n, R)) (mk : forall g : GL n R, motive (ProjGenLinGroup.mk g)) :
 motive g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_smul`：det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^
 Fintype.card n * det A
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toPGL_surj_of_roots
    (hR : ∀ r : Rˣ, ∃ k : Rˣ, k ^ Fintype.card n = r) :
    Function.Surjective (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)) := fun g ↦ by
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g =>
  obtain ⟨r, hr⟩ : ∃ r : Rˣ, r ^ Fintype.card n * g.det = 1 := by
    obtain ⟨r, hr⟩ := hR g.det⁻¹
    exact ⟨r, by simpa [mul_eq_one_iff_eq_inv] using hr⟩
  simp only [Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val,
    GeneralLinearGroup.val_det_apply, ← Matrix.det_smul g.1 r.1, Units.val_one] at hr
  use QuotientGroup.mk ⟨r.1 • g.1, hr⟩
  simp only [ProjectiveSpecialLinearGroup.toPGL_mk, mk_eq_mk_iff]
  refine ⟨r⁻¹, Units.ext ?_⟩
  simp only [Units.val_mul, coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar]
  simp [← Matrix.mul_smul, ← Matrix.diagonal_smul, Pi.smul_def, smul_eq_mul]
/-
**Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_iff** 是 Mathlib 中的一个引理，位于命名空间 `
Matrix.ProjectiveSpecialLinearGroup`。
形式化陈述：toPGL_surj_iff [Nonempty n] : Function.Surjective (ProjectiveSpecialLinear
Group.toPGL (n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.GeneralLinearGroup.det_surjective`：det_surjective [Nonempty n] : 
Function.Surjective (det : GL n R -> Rˣ)
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Matrix.SpecialLinearGroup.coeToGL_det`：coeToGL_det (g : SpecialLinearGro
up n R) : Matrix.GeneralLinearGroup.det (g : GL n R) = 1
· 使用定理 `Matrix.GeneralLinearGroup.det_scalar`：det_scalar (u : Rˣ) : det (scalar 
n u) = u ^ Fintype.card n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots`：toPGL_surj_of_r
oots (hR : forall r : Rˣ, exists k : Rˣ, k ^ Fintype.card n = r) : Function.Surj
ective (ProjectiveSpecialLinearGroup.toPGL (n
-/
lemma toPGL_surj_iff [Nonempty n] :
    Function.Surjective (ProjectiveSpecialLinearGroup.toPGL (n := n) (R := R)) ↔
      ∀ r : Rˣ, ∃ k : Rˣ, k ^ Fintype.card n = r := by
  refine ⟨fun h r ↦ ?_, ProjectiveSpecialLinearGroup.toPGL_surj_of_roots⟩
  obtain ⟨A, hA⟩ := GeneralLinearGroup.det_surjective (n := n) r
  obtain ⟨X, hX⟩ := h (.mk A)
  induction X using QuotientGroup.induction_on with | H X =>
  obtain ⟨u, hu⟩ : ∃ u, toGL X * (GeneralLinearGroup.scalar n) u = A := by
    simpa [mk_eq_mk_iff] using hX
  exact ⟨u, by simpa [hA] using congr(Matrix.GeneralLinearGroup.det $hu)⟩

open Polynomial in
/-- An isomorphism between `PGL(n, F)` and `PSL(n, F)` in the case of an algebraically closed field
  induced from the natural inclusion map. -/
/-
**Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty** 是 Mathlib 中的
一个定义，位于命名空间 `Matrix.ProjectiveSpecialLinearGroup`。
形式化陈述：isoPSLOfAlgClosedOfNonempty [Nonempty n] {F : Type*} [Field F] [IsAlgClose
d F] : PGL(n, F) ≃* ProjectiveSpecialLinearGroup n F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism between `PGL(n, F)` and `PSL(n, F)` in the case of an algebraical
ly closed field
  induced from the natural inclusion map.
-/
noncomputable def isoPSLOfAlgClosedOfNonempty [Nonempty n] {F : Type*} [Field F] [IsAlgClosed F] :
    PGL(n, F) ≃* ProjectiveSpecialLinearGroup n F :=
  MulEquiv.symm (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
    Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r => by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ Fintype.card n - C r.1 : F[X]) (by
    simp [Polynomial.degree_X_pow_sub_C Fintype.card_pos])
  have hx' : x ≠ 0 := by aesop
  exact ⟨⟨x, x⁻¹, mul_inv_cancel₀ hx', inv_mul_cancel₀ hx'⟩, by
    simpa [Units.ext_iff, sub_eq_zero] using hx⟩⟩)

/-- An isomorphism between `PGL(n, F)` and `PSL(n, F)` in the case of an algebraically closed field
  induced from the natural inclusion map where when `n` is empty it gives a junk isomorphism. -/
/-
**Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed** 是 Mathlib 中的一个定义，位于命名空
间 `Matrix.ProjectiveSpecialLinearGroup`。
形式化陈述：isoPSLOfAlgClosed {F : Type*} [Field F] [IsAlgClosed F] : PGL(n, F) ≃* Pro
jectiveSpecialLinearGroup n F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism between `PGL(n, F)` and `PSL(n, F)` in the case of an algebraical
ly closed field
  induced from the natural inclusion map where when `n` is empty it gives a junk
 isomorphism.
-/
noncomputable def isoPSLOfAlgClosed {F : Type*} [Field F] [IsAlgClosed F] :
    PGL(n, F) ≃* ProjectiveSpecialLinearGroup n F :=
  open scoped Classical in
  if h : Nonempty n then isoPSLOfAlgClosedOfNonempty else
  have : IsEmpty n := by simpa using h
  have : Subsingleton (PGL(n, F)) := mk_surjective.subsingleton
  MulEquiv.symm (MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
    ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective, Function.surjective_to_subsingleton _⟩)

end ProjectiveSpecialLinearGroup

end isoPSL

namespace ProjGenLinGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] {M : Type*} [Monoid M]

/-- Lift a monoid homomorphism `f : GL n R →* M` that vanishes on all scalar matrices
to a homomorphism from `PGL(n, R)`. -/
/-
**Matrix.ProjGenLinGroup.lift** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.ProjGenLinGroup`
。
形式化陈述：lift (f : GL n R ->* M) (hf : f.comp (GeneralLinearGroup.scalar n) = 1) : 
PGL(n, R) ->* M
参数：f : GL n R ->* M；hf : f.comp (GeneralLinearGroup.scalar n) = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a monoid homomorphism `f : GL n R →* M` that vanishes on all scalar matrice
s
to a homomorphism from `PGL(n, R)`.
-/
def lift (f : GL n R →* M) (hf : f.comp (GeneralLinearGroup.scalar n) = 1) :
    PGL(n, R) →* M :=
  QuotientGroup.lift _ f <| by
    rwa [GeneralLinearGroup.center_eq_range_scalar, MonoidHom.range_le_ker_iff]

@[simp]
/-
**Matrix.ProjGenLinGroup.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.ProjGenLinGro
up`。
形式化陈述：lift_mk {f : GL n R ->* M} (hf) (g : GL n R) : lift f hf (mk g) = f g
参数：hf；g : GL n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk {f : GL n R →* M} (hf) (g : GL n R) : lift f hf (mk g) = f g := by
  rfl

@[simp]
/-
**Matrix.ProjGenLinGroup.lift_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.ProjGenL
inGroup`。
形式化陈述：lift_comp_mk {f : GL n R ->* M} (hf) : (lift f hf).comp mk = f
参数：hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_mk {f : GL n R →* M} (hf) : (lift f hf).comp mk = f := by
  rfl

/-- Given an action of `GL n R` such that the scalar matrices act trivially,
define an action of `PGL n R`. -/
@[instance_reducible]
/-
**Matrix.ProjGenLinGroup.mulActionOfGL** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.ProjGen
LinGroup`。
形式化陈述：mulActionOfGL {α : Type*} [MulAction (GL n R) α] (h : forall (u : Rˣ) (a :
 α), GeneralLinearGroup.scalar n u • a = a) : MulAction (PGL(n, R)) α
参数：GL n R；h : forall (u : Rˣ) (a : α), GeneralLinearGroup.scalar n u • a = a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an action of `GL n R` such that the scalar matrices act trivially,
define an action of `PGL n R`.
-/
def mulActionOfGL {α : Type*} [MulAction (GL n R) α]
    (h : ∀ (u : Rˣ) (a : α), GeneralLinearGroup.scalar n u • a = a) :
    MulAction (PGL(n, R)) α :=
  .ofEndHom <| lift MulAction.toEndHom <| by
    ext u
    funext a -- TODO: should we add an `ext` lemma for `Function.End`?
    exact h u a
/-
**Matrix.ProjGenLinGroup.mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.ProjGenLinGro
up`。
形式化陈述：mk_smul {α : Type*} [MulAction (GL n R) α] (h) (g : GL n R) (a : α) : letI
 : MulAction (PGL(n, R)) α
参数：GL n R；h；g : GL n R；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul {α : Type*} [MulAction (GL n R) α] (h) (g : GL n R) (a : α) :
    letI : MulAction (PGL(n, R)) α := mulActionOfGL h
    mk g • a = g • a := by
  rfl

/-- The monoid hom between `PGL(n, R)` and `PGL(n, S)` induced by a
  ring homomorphism `f : R →+* S`. -/
/-
**Matrix.ProjGenLinGroup.map** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.ProjGenLinGroup`。
形式化陈述：map {S : Type*} [CommRing S] (f : R ->+* S) : PGL(n, R) ->* PGL(n, S)
参数：f : R ->+* S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.GeneralLinearGroup.map_center_le`：map_center_le {S : Type*} [Comm
Ring S] (f : R ->+* S) : Subgroup.center (GL n R) <= (Subgroup.center (GL n S)).
comap (map f)

--- 原说明 ---
The monoid hom between `PGL(n, R)` and `PGL(n, S)` induced by a
  ring homomorphism `f : R →+* S`.
-/
def map {S : Type*} [CommRing S] (f : R →+* S) : PGL(n, R) →* PGL(n, S) :=
  QuotientGroup.map _ _ (GeneralLinearGroup.map (n := n) f) <| GeneralLinearGroup.map_center_le f

@[simp]
/-
**Matrix.ProjGenLinGroup.map_id** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.ProjGenLinGrou
p`。
形式化陈述：map_id : map (RingHom.id R) = MonoidHom.id (PGL(n, R))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.map_id`：map_id (h : N <= Subgroup.comap (MonoidHom.id _) N
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Subgroup.comap_id`：comap_id (K : Subgroup N) : K.comap (MonoidHom.id _) 
= K
-/
lemma map_id : map (RingHom.id R) = MonoidHom.id (PGL(n, R)) := QuotientGroup.map_id _

@[simp]
/-
**Matrix.ProjGenLinGroup.map_mk** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.ProjGenLinGrou
p`。
形式化陈述：map_mk {S : Type*} [CommRing S] (f : R ->+* S) (g : GL n R) : map f (mk g)
 = mk (GeneralLinearGroup.map f g)
参数：f : R ->+* S；g : GL n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_mk {S : Type*} [CommRing S] (f : R →+* S) (g : GL n R) :
    map f (mk g) = mk (GeneralLinearGroup.map f g) := rfl
/-
**Matrix.ProjGenLinGroup.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.ProjGenLinGr
oup`。
形式化陈述：map_comp {S T : Type*} [CommRing S] [CommRing T] (f : R ->+* S) (g : S ->+
* T) : map (n
参数：f : R ->+* S；g : S ->+* T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Matrix.ProjGenLinGroup.induction_on`：induction_on {motive : PGL(n, R) ->
 Prop} (g : PGL(n, R)) (mk : forall g : GL n R, motive (ProjGenLinGroup.mk g)) :
 motive g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp {S T : Type*} [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    map (n := n) (g.comp f) = (map g).comp (map f) := by
  ext g
  induction g using Matrix.ProjGenLinGroup.induction_on with | mk g => simp

variable [Fact (Even (Fintype.card n))] [LinearOrder R] [IsStrictOrderedRing R]

/-- In case of an even dimension, the sign of the determinant of `g : PGL(n, R)` is well-defined. -/
/-
**Matrix.ProjGenLinGroup.signDet** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.ProjGenLinGro
up`。
形式化陈述：signDet : PGL(n, R) ->* SignTypeˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In case of an even dimension, the sign of the determinant of `g : PGL(n, R)` is 
well-defined.
-/
def signDet : PGL(n, R) →* SignTypeˣ :=
  lift ((Units.map signHom.toMonoidHom).comp GeneralLinearGroup.det) <| by
    ext u
    simp [← sign_pow, Even.pow_pos Fact.out]
/-
**Matrix.ProjGenLinGroup.signDet_mk** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.ProjGenLin
Group`。
形式化陈述：signDet_mk (g : GL n R) : signDet (mk g) = Units.map signHom.toMonoidHom g
.det
参数：g : GL n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem signDet_mk (g : GL n R) : signDet (mk g) = Units.map signHom.toMonoidHom g.det := by
  rfl

@[simp]
/-
**Matrix.ProjGenLinGroup.val_signDet_mk** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.ProjGe
nLinGroup`。
形式化陈述：val_signDet_mk (g : GL n R) : (signDet (mk g) : SignType) = .sign g.det.va
l
参数：g : GL n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_signDet_mk (g : GL n R) : (signDet (mk g) : SignType) = .sign g.det.val := by
  rfl

end ProjGenLinGroup

end Matrix

