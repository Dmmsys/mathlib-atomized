/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.Normed.Module.RCLike.Extend
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Hahn-Banach theorem for polynormable spaces

In this file, we prove the analytic Hahn-Banach theorem for polynormable spaces over a field
satisfying `IsRCLikeNormedField`. For any continuous linear functional on a subspace, we can extend
it to the entire space. Note that we cannot use `LocallyConvexSpace` because an
`IsRCLikeNormedField` has no order structure.

We prove
* `Module.Dual.exists_continuous_extension_of_le_seminorm`: Hahn-Banach theorem for linear
  functionals dominated by a continuous seminorm on polynormable spaces over a field satisfying
  `IsRCLikeNormedField`.
* `StrongDual.exists_extension`: Hahn-Banach theorem for continuous linear functionals on
  polynormable spaces over fields satisfying `IsRCLikeNormedField`.

-/

public section

open Module Topology RCLike

open scoped ComplexConjugate

variable {𝕜 E : Type*} [AddCommGroup E]

/-
**Module.Dual.exists_extension_of_le_seminorm_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Dual.exists_extension_of_le_seminorm_real [Module Real E] (S : Subs
pace Real E) (f : Dual Real S) {p : Seminorm Real E} (hp : forall x, f x <= p x)
 : exists g : Dual Real E, (forall x : S, g x = f x) ∧ forall x, |g x| <= p x
参数：S : Subspace Real E；f : Dual Real S；hp : forall x, f x <= p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_extension_of_le_sublinear`：exists_extension_of_le_sublinear (f : 
E ->ₗ.[Real] Real) (N : E -> Real) (N_hom : forall c : Real, 0 < c -> forall x, 
N (c • x) = c * N x) (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SubadditiveHomClass.map_add_le_add`：∀ {F : Type u_7} {α : outParam (Type
 u_8)} {β : outParam (Type u_9)} {inst : Add α} {inst_1 : Add β} {inst_2 : LE β}
   {inst_3 : FunLike F α…
· 使用定理 `AddGroupSeminormClass.toSubadditiveHomClass`：∀ {F : Type u_7} {α : outPa
ram (Type u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommM
onoid β}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Seminorm.abs_le_of_le`：∀ {E : Type u_6} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] {p : Seminorm ℝ E} {f : E →ₗ[ℝ] ℝ},   (∀ (x : E), f x ≤ p x
) → ∀ (x : …
-/
theorem Module.Dual.exists_extension_of_le_seminorm_real [Module ℝ E]
    (S : Subspace ℝ E) (f : Dual ℝ S)
    {p : Seminorm ℝ E} (hp : ∀ x, f x ≤ p x) :
    ∃ g : Dual ℝ E, (∀ x : S, g x = f x) ∧ ∀ x, |g x| ≤ p x := by
  obtain ⟨g, hg, hl⟩ := by
    refine exists_extension_of_le_sublinear ⟨S, f⟩ p (fun _ hc _ => ?_) ?_ hp
    · simp [map_smul_eq_mul, abs_of_nonneg hc.le]
    · exact fun x y => map_add_le_add p x y
  exact ⟨g, hg, p.abs_le_of_le hl⟩

variable [NormedField 𝕜] [IsRCLikeNormedField 𝕜]
/-
**Module.Dual.exists_extension_of_le_seminorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Dual.exists_extension_of_le_seminorm [Module 𝕜 E] (S : Submodule 𝕜 
E) (f : Dual 𝕜 S) {p : Seminorm 𝕜 E} (hp : forall x, ‖f x‖ <= p x) : exists g : 
Dual 𝕜 E, (forall x : S, g x = f x) ∧ forall x, ‖g x‖ <= p x
参数：S : Submodule 𝕜 E；f : Dual 𝕜 S；hp : forall x, ‖f x‖ <= p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.restrictScalars`：IsScalarTower.restrictScalars [Module S M
] : letI
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Module.Dual.exists_extension_of_le_seminorm_real`：Module.Dual.exists_ext
ension_of_le_seminorm_real [Module Real E] (S : Subspace Real E) (f : Dual Real 
S) {p : Seminorm Real E} (hp : forall …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `RCLike.re_le_norm`：re_le_norm (z : K) : re z <= ‖z‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Dual.extendRCLike_apply`：extendRCLike_apply (fr : Dual Real F) (x
 : F) : fr.extendRCLike x = (fr x : 𝕜) - (I : 𝕜) * (fr ((I : 𝕜) • x) : 𝕜)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.coe_smul`：coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • (
x : M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `RCLike.I_im`：I_im (z : K) : im z * im (I : K) = im z
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
（共 35 条，此处仅展示前 30 条）
-/
theorem Module.Dual.exists_extension_of_le_seminorm [Module 𝕜 E] (S : Submodule 𝕜 E) (f : Dual 𝕜 S)
    {p : Seminorm 𝕜 E} (hp : ∀ x, ‖f x‖ ≤ p x) :
    ∃ g : Dual 𝕜 E, (∀ x : S, g x = f x) ∧ ∀ x, ‖g x‖ ≤ p x := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : Module ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .restrictScalars _ _ _
  let fr : Dual ℝ S := reLm.comp (f.restrictScalars ℝ)
  obtain ⟨g, (hg : ∀ x : S, g x = fr x), hgp⟩ :=
    fr.exists_extension_of_le_seminorm_real (S.restrictScalars ℝ) (p := p.restrictScalars ℝ)
      fun x ↦ (re_le_norm (f x)).trans (hp x)
  refine ⟨g.extendRCLike, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [g.extendRCLike_apply, ← Submodule.coe_smul, hg, hg]
    simp [fr, mul_comm I]
  · apply norm_extendRCLike_le_seminorm
    exact hgp

variable [TopologicalSpace E]

/-- **Hahn-Banach theorem** for linear functionals dominated by a continuous seminorm on
polynormable spaces over `ℝ`. -/
/-
**Module.Dual.exists_continuous_extension_of_le_seminorm_real** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：Module.Dual.exists_continuous_extension_of_le_seminorm_real [Module Real E
] [PolynormableSpace Real E] (S : Subspace Real E) (f : Dual Real S) {p : Semino
rm Real E} (hp_cont : Continuous p) (hp : forall x, f x <= p x) : exists g : Str
ongDual Real E, (forall x : S, g x = f x) ∧ forall x, |g x| <= p x
参数：S : Subspace Real E；f : Dual Real S；hp_cont : Continuous p；hp : forall x, f x
 <= p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Dual.exists_extension_of_le_seminorm_real`：Module.Dual.exists_ext
ension_of_le_seminorm_real [Module Real E] (S : Subspace Real E) (f : Dual Real 
S) {p : Seminorm Real E} (hp : forall …
· 使用定理 `WithSeminorms.continuous_real_rng`：continuous_real_rng [Module Real E] [
TopologicalSpace E] {p : ι -> Seminorm Real E} (hp : WithSeminorms p) (f : E ->ₗ
[Real] Real) (hf : exis…
· 使用定理 `PolynormableSpace.withSeminorms`：PolynormableSpace.withSeminorms [Polyno
rmableSpace 𝕜 E] : WithSeminorms (fun p : {p : Seminorm 𝕜 E // Continuous p} => 
p.1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|

--- 原说明 ---
**Hahn-Banach theorem** for linear functionals dominated by a continuous seminor
m on
polynormable spaces over `ℝ`.
-/
theorem Module.Dual.exists_continuous_extension_of_le_seminorm_real
    [Module ℝ E] [PolynormableSpace ℝ E] (S : Subspace ℝ E) (f : Dual ℝ S)
    {p : Seminorm ℝ E} (hp_cont : Continuous p) (hp : ∀ x, f x ≤ p x) :
    ∃ g : StrongDual ℝ E, (∀ x : S, g x = f x) ∧ ∀ x, |g x| ≤ p x := by
  obtain ⟨g, hg, hl⟩ := f.exists_extension_of_le_seminorm_real S hp
  exact ⟨⟨g, (PolynormableSpace.withSeminorms ℝ E).continuous_real_rng g
    ⟨{⟨p, hp_cont⟩}, 1, fun x ↦ by simpa using (le_abs_self _).trans (hl x)⟩⟩, hg, hl⟩

variable [Module 𝕜 E] [PolynormableSpace 𝕜 E]

/-- **Hahn-Banach theorem** for linear functionals dominated by a continuous seminorm on
polynormable spaces over fields satisfying `IsRCLikeNormedField`. -/
/-
**Module.Dual.exists_continuous_extension_of_le_seminorm** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Module.Dual.exists_continuous_extension_of_le_seminorm (S : Submodule 𝕜 E)
 (f : Dual 𝕜 S) {p : Seminorm 𝕜 E} (hp_cont : Continuous p) (hp : forall x, ‖f x
‖ <= p x) : exists g : StrongDual 𝕜 E, (forall x : S, g x = f x) ∧ forall x, ‖g 
x‖ <= p x
参数：S : Submodule 𝕜 E；f : Dual 𝕜 S；hp_cont : Continuous p；hp : forall x, ‖f x‖ <=
 p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Dual.exists_extension_of_le_seminorm`：Module.Dual.exists_extensio
n_of_le_seminorm [Module 𝕜 E] (S : Submodule 𝕜 E) (f : Dual 𝕜 S) {p : Seminorm 𝕜
 E} (hp : forall x, ‖f x‖ <= p x)…
· 使用定理 `WithSeminorms.continuous_normedSpace_rng`：continuous_normedSpace_rng (F)
 [SeminormedAddCommGroup F] [NormedSpace 𝕝₂ F] [TopologicalSpace E] {p : ι -> Se
minorm 𝕝 E} (hp : WithSeminorm…
· 使用定理 `PolynormableSpace.withSeminorms`：PolynormableSpace.withSeminorms [Polyno
rmableSpace 𝕜 E] : WithSeminorms (fun p : {p : Seminorm 𝕜 E // Continuous p} => 
p.1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
**Hahn-Banach theorem** for linear functionals dominated by a continuous seminor
m on
polynormable spaces over fields satisfying `IsRCLikeNormedField`.
-/
theorem Module.Dual.exists_continuous_extension_of_le_seminorm (S : Submodule 𝕜 E) (f : Dual 𝕜 S)
    {p : Seminorm 𝕜 E} (hp_cont : Continuous p) (hp : ∀ x, ‖f x‖ ≤ p x) :
    ∃ g : StrongDual 𝕜 E, (∀ x : S, g x = f x) ∧ ∀ x, ‖g x‖ ≤ p x := by
  obtain ⟨g, hg, hle⟩ := Dual.exists_extension_of_le_seminorm S f hp
  refine ⟨⟨g, (PolynormableSpace.withSeminorms 𝕜 E).continuous_normedSpace_rng 𝕜 g ?_⟩, hg, hle⟩
  exact ⟨{⟨p, hp_cont⟩}, 1, by simpa⟩

/-- **Hahn-Banach theorem** for continuous linear functionals on polynormable spaces over a field
satisfying `IsRCLikeNormedField`. -/
/-
**StrongDual.exists_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrongDual.exists_extension {𝕜} [NontriviallyNormedField 𝕜] [IsRCLikeNorme
dField 𝕜] [Module 𝕜 E] [PolynormableSpace 𝕜 E] (S : Submodule 𝕜 E) (f : StrongDu
al 𝕜 S) : exists g : StrongDual 𝕜 E, forall x : S, g x = f x
参数：S : Submodule 𝕜 E；f : StrongDual 𝕜 S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.exists_le_comp_of_isInducing`：Seminorm.exists_le_comp_of_isIndu
cing {p : Seminorm 𝕜 E} (hp : Continuous p) [PolynormableSpace 𝕜₂ F] {f : E ->ₛₗ
[σ₁₂] F} (hf : IsInducing f…
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Module.Dual.exists_continuous_extension_of_le_seminorm`：Module.Dual.exis
ts_continuous_extension_of_le_seminorm (S : Submodule 𝕜 E) (f : Dual 𝕜 S) {p : S
eminorm 𝕜 E} (hp_cont : Continuous p) (hp : …

--- 原说明 ---
**Hahn-Banach theorem** for continuous linear functionals on polynormable spaces
 over a field
satisfying `IsRCLikeNormedField`.
-/
theorem StrongDual.exists_extension {𝕜} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [Module 𝕜 E] [PolynormableSpace 𝕜 E] (S : Submodule 𝕜 E) (f : StrongDual 𝕜 S) :
    ∃ g : StrongDual 𝕜 E, ∀ x : S, g x = f x := by
  obtain ⟨q, hq_cont, hq⟩ := Seminorm.exists_le_comp_of_isInducing (f := S.subtype)
    (p := f.toSeminorm) f.continuous.norm IsInducing.subtypeVal
  obtain ⟨g, hg, _⟩ := Dual.exists_continuous_extension_of_le_seminorm S f.toLinearMap hq_cont hq
  exact ⟨g, hg⟩

variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  [ContinuousSMul 𝕜 F] [T2Space F]

set_option backward.isDefEq.respectTransparency.types false in
/-- Corollary of the polynormable **Hahn-Banach theorem**: if `f : S → F` is a continuous
linear map with finite-dimensional range, then `f` extends to a continuous linear map on the whole
space. -/
/-
**ContinuousLinearMap.exist_extension_of_finiteDimensional_range** 是 Mathlib 中的一
个引理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.exist_extension_of_finiteDimensional_range {S : Submod
ule 𝕜 E} (f : S ->L[𝕜] F) [FiniteDimensional 𝕜 f.range] : exists g : E ->L[𝕜] F,
 f = g.comp S.subtypeL
参数：f : S ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用引理 `Module.Basis.equivFunL_symm_apply_repr`：equivFunL_symm_apply_repr (v : B
asis ι 𝕜 E) (x : E) : v.equivFunL.symm (v.repr x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `StrongDual.exists_extension`：StrongDual.exists_extension {𝕜} [Nontrivial
lyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [Module 𝕜 E] [PolynormableSpace 𝕜 E] (S
 : Submodule 𝕜 E)…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Corollary of the polynormable **Hahn-Banach theorem**: if `f : S → F` is a conti
nuous
linear map with finite-dimensional range, then `f` extends to a continuous linea
r map on the whole
space.
-/
lemma ContinuousLinearMap.exist_extension_of_finiteDimensional_range {S : Submodule 𝕜 E}
    (f : S →L[𝕜] F) [FiniteDimensional 𝕜 f.range] :
    ∃ g : E →L[𝕜] F, f = g.comp S.subtypeL := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let b := Module.finBasis 𝕜 f.range
  let e := b.equivFunL
  let fi := fun i ↦ (LinearMap.toContinuousLinearMap (b.coord i)).comp
    (f.codRestrict _ <| LinearMap.mem_range_self _)
  choose gi hgf using fun i ↦ StrongDual.exists_extension S (fi i)
  use f.range.subtypeL.comp <| e.symm.toContinuousLinearMap.comp (.pi gi)
  ext x
  simp [fi, e, hgf]

/-- A finite-dimensional submodule of a polynormable space over a field satisfying
`IsRCLikeNormedField` is `Submodule.ClosedComplemented`. -/
/-
**Submodule.ClosedComplemented.of_finiteDimensional** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：Submodule.ClosedComplemented.of_finiteDimensional [PolynormableSpace 𝕜 F] 
(S : Submodule 𝕜 F) [FiniteDimensional 𝕜 S] : S.ClosedComplemented
参数：S : Submodule 𝕜 F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.exist_extension_of_finiteDimensional_range`：Continuo
usLinearMap.exist_extension_of_finiteDimensional_range {S : Submodule 𝕜 E} (f : 
S ->L[𝕜] F) [FiniteDimensional 𝕜 f.range] : exists g…
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A finite-dimensional submodule of a polynormable space over a field satisfying
`IsRCLikeNormedField` is `Submodule.ClosedComplemented`.
-/
lemma Submodule.ClosedComplemented.of_finiteDimensional [PolynormableSpace 𝕜 F] (S : Submodule 𝕜 F)
    [FiniteDimensional 𝕜 S] : S.ClosedComplemented := by
  let ⟨g, hg⟩ := (ContinuousLinearMap.id 𝕜 S).exist_extension_of_finiteDimensional_range
  exact ⟨g, DFunLike.congr_fun hg.symm⟩
