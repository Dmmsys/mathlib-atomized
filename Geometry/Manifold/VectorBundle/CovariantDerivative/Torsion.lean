/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-! # Torsion of an affine connection

We define the torsion tensor of an affine connection, i.e. a covariant derivative on the tangent
bundle `TM` of some manifold `M`.

## Main definitions and results

* `IsCovariantDerivativeOn.torsion`: the torsion tensor of an unbundled covariant derivative
  on `TM`
* `CovariantDerivative.torsion`: the torsion tensor of a bundled covariant derivative on `TM`
* `CovariantDerivative.torsion_eq_zero_iff`: the torsion tensor of a bundled covariant derivative
  `∇` vanishes if and only if `∇_X Y - ∇_Y X = [X, Y]` for all differentiable vector fields
  `X` and `Y`.

-/

public noncomputable section

open Bundle Set NormedSpace FiberBundle
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

/-! ## Torsion tensor of an unbundled covariant derivative on `TM` on a set `s` -/
namespace IsCovariantDerivativeOn

/-- The torsion of a covariant derivative on the tangent bundle `TM`, as a bare function.
Prefer to use `IsCovariantDerivativeOn.torsion` (which is a 2-tensor) instead. -/
/-
**IsCovariantDerivativeOn.torsionAux** 是 Mathlib 中的一个定义，位于命名空间 `IsCovariantDeriv
ativeOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The torsion of a covariant derivative on the tangent bundle `TM`, as a bare func
tion.
Prefer to use `IsCovariantDerivativeOn.torsion` (which is a 2-tensor) instead.
-/
private def torsionAux
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y x ↦ cov Y x (X x) - cov X x (Y x) - VectorField.mlieBracket I X Y x

variable [IsManifold I 2 M] [CompleteSpace E]
  {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
  {X X' Y : Π x : M, TangentSpace I x}
/-
**IsCovariantDerivativeOn.torsionAux_tensorial** 是 Mathlib 中的一个定理，位于命名空间 `IsCova
riantDerivativeOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem torsionAux_tensorial₁ (hcov : IsCovariantDerivativeOn E cov) (x : M)
    (Y : Π x, TangentSpace I x) :
    TensorialAt I E (torsionAux cov · Y x) x where
  smul hf hX := by
    simp [torsionAux, hcov.leibniz hX hf, VectorField.mlieBracket_smul_left hf hX]
    module
  add hX hX' := by
    simp [torsionAux, hcov.add hX hX', VectorField.mlieBracket_add_left hX hX']
    module
/-
**IsCovariantDerivativeOn.torsionAux_tensorial** 是 Mathlib 中的一个定理，位于命名空间 `IsCova
riantDerivativeOn`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem torsionAux_tensorial₂ (hcov : IsCovariantDerivativeOn E cov) (x : M)
    (X : Π x, TangentSpace I x) :
    TensorialAt I E (torsionAux cov X · x) x where
  smul hf hY := by
    simp [torsionAux, hcov.leibniz hY hf, VectorField.mlieBracket_smul_right hf hY]
    module
  add hY hY' := by
    simp [torsionAux, hcov.add hY hY', VectorField.mlieBracket_add_right hY hY']
    module

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- The torsion tensor of an unbundled covariant derivative on `TM`. -/
/-
**IsCovariantDerivativeOn.torsion** 是 Mathlib 中的一个定义，位于命名空间 `IsCovariantDerivati
veOn`。
形式化陈述：torsion (hcov : IsCovariantDerivativeOn E cov univ) (x : M) : TangentSpace
 I x ->L[𝕜] TangentSpace I x ->L[𝕜] TangentSpace I x
参数：hcov : IsCovariantDerivativeOn E cov univ；x : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Tors
ion.0.IsCovariantDerivativeOn.torsionAux_tensorial₁`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Tors
ion.0.IsCovariantDerivativeOn.torsionAux_tensorial₂`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
The torsion tensor of an unbundled covariant derivative on `TM`.
-/
noncomputable def torsion (hcov : IsCovariantDerivativeOn E cov univ) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] TangentSpace I x :=
  TensorialAt.mkHom₂ (torsionAux cov · · x) _
    (fun τ _ ↦ hcov.torsionAux_tensorial₁ x τ)
    (fun σ _ ↦ hcov.torsionAux_tensorial₂ x σ)
/-
**IsCovariantDerivativeOn.torsion_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsCovariantDe
rivativeOn`。
形式化陈述：torsion_apply (hcov : IsCovariantDerivativeOn E cov univ) {x} {X : Π x : M
, TangentSpace I x} (hX : MDiffAt (T% X) x) {Y : Π x : M, TangentSpace I x} (hY 
: MDiffAt (T% Y) x) : torsion hcov x (X x) (Y x) = cov Y x (X x) - cov X x (Y x)
 - VectorField.mlieBracket I X Y x
参数：hcov : IsCovariantDerivativeOn E cov univ；hX : MDiffAt (T% X) x；hY : MDiffAt 
(T% Y) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `TensorialAt.mkHom₂_apply`：mkHom₂_apply {Φ : (Π x : M, V x) -> (Π x : M, 
V' x) -> A} {x} (hΦ₁ : forall τ, MDiffAt (T% τ) x -> TensorialAt I F (Φ · τ) x) 
(hΦ₂ : forall …
· 使用定理 `instContMDiffVectorBundleOfNatWithTopENatTangentSpaceOfIsManifold`：∀ {𝕜 
: Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAd
dCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Tors
ion.0.IsCovariantDerivativeOn.torsionAux_tensorial₁`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Tors
ion.0.IsCovariantDerivativeOn.torsionAux_tensorial₂`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 E] {H : Type u_…
-/
theorem torsion_apply (hcov : IsCovariantDerivativeOn E cov univ) {x}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    torsion hcov x (X x) (Y x) = cov Y x (X x) - cov X x (Y x) - VectorField.mlieBracket I X Y x :=
  TensorialAt.mkHom₂_apply _ _ hX hY
/-
**IsCovariantDerivativeOn.torsion_apply_eq_extend** 是 Mathlib 中的一个定理，位于命名空间 `IsC
ovariantDerivativeOn`。
形式化陈述：torsion_apply_eq_extend (hcov : IsCovariantDerivativeOn E cov univ) {x} (X
₀ Y₀ : TangentSpace I x) : torsion hcov x X₀ Y₀ = cov (extend E Y₀) x X₀ - cov (
extend E X₀) x Y₀ - VectorField.mlieBracket I (extend E X₀) (extend E Y₀) x
参数：hcov : IsCovariantDerivativeOn E cov univ；X₀ Y₀ : TangentSpace I x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FiberBundle.extend_apply_self`：∀ {B : Type u_2} (F : Type u_3) {E : B → 
Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : 
(x : B) → Topologic…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem torsion_apply_eq_extend (hcov : IsCovariantDerivativeOn E cov univ) {x}
    (X₀ Y₀ : TangentSpace I x) :
    torsion hcov x X₀ Y₀ =
      cov (extend E Y₀) x X₀ - cov (extend E X₀) x Y₀ -
        VectorField.mlieBracket I (extend E X₀) (extend E Y₀) x := by
  simp [torsion, torsionAux, TensorialAt.mkHom₂_apply_eq_extend]

variable (X) in
@[simp]
/-
**IsCovariantDerivativeOn.torsion_self** 是 Mathlib 中的一个引理，位于命名空间 `IsCovariantDer
ivativeOn`。
形式化陈述：torsion_self (hcov : IsCovariantDerivativeOn E cov univ) (X₀ : TangentSpac
e I x) : hcov.torsion x X₀ X₀ = 0
参数：hcov : IsCovariantDerivativeOn E cov univ；X₀ : TangentSpace I x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCovariantDerivativeOn.torsion_apply_eq_extend`：torsion_apply_eq_extend
 (hcov : IsCovariantDerivativeOn E cov univ) {x} (X₀ Y₀ : TangentSpace I x) : to
rsion hcov x X₀ Y₀ = cov (extend E Y₀…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `VectorField.mlieBracket_self`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 
: NormedAddCommGro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma torsion_self (hcov : IsCovariantDerivativeOn E cov univ) (X₀ : TangentSpace I x) :
    hcov.torsion x X₀ X₀ = 0 := by
  simp [torsion_apply_eq_extend]

variable (X Y) in
/-
**IsCovariantDerivativeOn.torsion_antisymm** 是 Mathlib 中的一个引理，位于命名空间 `IsCovarian
tDerivativeOn`。
形式化陈述：torsion_antisymm (hcov : IsCovariantDerivativeOn E cov univ) (X₀ Y₀ : Tang
entSpace I x) : hcov.torsion x X₀ Y₀ = - hcov.torsion x Y₀ X₀
参数：hcov : IsCovariantDerivativeOn E cov univ；X₀ Y₀ : TangentSpace I x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCovariantDerivativeOn.torsion_apply_eq_extend`：torsion_apply_eq_extend
 (hcov : IsCovariantDerivativeOn E cov univ) {x} (X₀ Y₀ : TangentSpace I x) : to
rsion hcov x X₀ Y₀ = cov (extend E Y₀…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `VectorField.mlieBracket_swap`：mlieBracket_swap : mlieBracket I V W = - m
lieBracket I W V
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.neg_eq_eval`：neg_eq_eval [AddCommGroup M] [Semi
ring S] [Module S M] [Ring R] [Module R M] {l : NF R M} {l₀ : NF S M} (hl : l.ev
al = l₀.eval) {x : M} (h :…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₃`：sub_eq_eval₃ [Ring R] [AddCommGro
up M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::ᵣ l₁)
.eval - l₂.eval = l.eval) :…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 38 条，此处仅展示前 30 条）
-/
lemma torsion_antisymm (hcov : IsCovariantDerivativeOn E cov univ) (X₀ Y₀ : TangentSpace I x) :
    hcov.torsion x X₀ Y₀ = - hcov.torsion x Y₀ X₀ := by
  simp only [torsion_apply_eq_extend, neg_sub]
  rw [VectorField.mlieBracket_swap]
  dsimp
  module

end IsCovariantDerivativeOn

/-! ## Torsion tensor of a bundled covariant derivative on `TM` -/
namespace CovariantDerivative

open VectorField

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 E] [IsManifold I 2 M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  {X Y : Π x : M, TangentSpace I x}

/-- The torsion tensor of a covariant derivative on the tangent bundle of a manifold. -/
/-
**CovariantDerivative.torsion** 是 Mathlib 中的一个定义，位于命名空间 `CovariantDerivative`。
形式化陈述：torsion (x : M) : TangentSpace I x ->L[𝕜] TangentSpace I x ->L[𝕜] TangentS
pace I x
参数：x : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…

--- 原说明 ---
The torsion tensor of a covariant derivative on the tangent bundle of a manifold
.
-/
def torsion (x : M) : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] TangentSpace I x :=
  cov.isCovariantDerivativeOn.torsion x
/-
**CovariantDerivative.torsion_apply** 是 Mathlib 中的一个引理，位于命名空间 `CovariantDerivati
ve`。
形式化陈述：torsion_apply (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) : cov.torsio
n x (X x) (Y x) = cov Y x (X x) - cov X x (Y x) - mlieBracket I X Y x
参数：hX : MDiffAt (T% X) x；hY : MDiffAt (T% Y) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `TensorialAt.mkHom₂_apply`：mkHom₂_apply {Φ : (Π x : M, V x) -> (Π x : M, 
V' x) -> A} {x} (hΦ₁ : forall τ, MDiffAt (T% τ) x -> TensorialAt I F (Φ · τ) x) 
(hΦ₂ : forall …
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Tors
ion.0.IsCovariantDerivativeOn.torsionAux_tensorial₁`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Tors
ion.0.IsCovariantDerivativeOn.torsionAux_tensorial₂`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 E] {H : Type u_…
-/
lemma torsion_apply (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov.torsion x (X x) (Y x) = cov Y x (X x) - cov X x (Y x) - mlieBracket I X Y x := by
  unfold torsion IsCovariantDerivativeOn.torsion
  apply TensorialAt.mkHom₂_apply
  exacts [hX, hY]
/-
**CovariantDerivative.torsion_apply_eq_extend** 是 Mathlib 中的一个引理，位于命名空间 `Covaria
ntDerivative`。
形式化陈述：torsion_apply_eq_extend (X₀ Y₀ : TangentSpace I x) : cov.torsion x X₀ Y₀ =
 cov (extend E Y₀) x (extend E X₀ x) - cov (extend E X₀) x (extend E Y₀ x) - mli
eBracket I (extend E X₀) (extend E Y₀) x
参数：X₀ Y₀ : TangentSpace I x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `TensorialAt.mkHom₂_apply_eq_extend`：mkHom₂_apply_eq_extend {Φ : (Π x : M
, V x) -> (Π x : M, V' x) -> A} {x} (hΦ₁ : forall τ, MDiffAt (T% τ) x -> Tensori
alAt I F (Φ · τ) x) (hΦ₂…
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Tors
ion.0.IsCovariantDerivativeOn.torsionAux_tensorial₁`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `_private.Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Tors
ion.0.IsCovariantDerivativeOn.torsionAux_tensorial₂`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_
2 : NormedSpace 𝕜 E] {H : Type u_…
-/
lemma torsion_apply_eq_extend (X₀ Y₀ : TangentSpace I x) :
    cov.torsion x X₀ Y₀ =
      cov (extend E Y₀) x (extend E X₀ x) - cov (extend E X₀) x (extend E Y₀ x) -
        mlieBracket I (extend E X₀) (extend E Y₀) x := by
  unfold torsion IsCovariantDerivativeOn.torsion
  apply TensorialAt.mkHom₂_apply_eq_extend

@[simp]
/-
**CovariantDerivative.torsion_self** 是 Mathlib 中的一个引理，位于命名空间 `CovariantDerivativ
e`。
形式化陈述：torsion_self (X₀ : TangentSpace I x) : cov.torsion x X₀ X₀ = 0
参数：X₀ : TangentSpace I x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用引理 `IsCovariantDerivativeOn.torsion_self`：torsion_self (hcov : IsCovariantDe
rivativeOn E cov univ) (X₀ : TangentSpace I x) : hcov.torsion x X₀ X₀ = 0
· 使用引理 `CovariantDerivative.isCovariantDerivativeOn`：isCovariantDerivativeOn (co
v : CovariantDerivative I F V) {s : Set M} : IsCovariantDerivativeOn F cov s
-/
lemma torsion_self (X₀ : TangentSpace I x) : cov.torsion x X₀ X₀ = 0 :=
  cov.isCovariantDerivativeOn.torsion_self ..
/-
**CovariantDerivative.torsion_antisymm** 是 Mathlib 中的一个引理，位于命名空间 `CovariantDeriv
ative`。
形式化陈述：torsion_antisymm (X₀ Y₀ : TangentSpace I x) : cov.torsion x X₀ Y₀ = - cov.
torsion x Y₀ X₀
参数：X₀ Y₀ : TangentSpace I x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用引理 `IsCovariantDerivativeOn.torsion_antisymm`：torsion_antisymm (hcov : IsCov
ariantDerivativeOn E cov univ) (X₀ Y₀ : TangentSpace I x) : hcov.torsion x X₀ Y₀
 = - hcov.torsion x Y₀ X₀
· 使用引理 `CovariantDerivative.isCovariantDerivativeOn`：isCovariantDerivativeOn (co
v : CovariantDerivative I F V) {s : Set M} : IsCovariantDerivativeOn F cov s
-/
lemma torsion_antisymm (X₀ Y₀ : TangentSpace I x) : cov.torsion x X₀ Y₀ = - cov.torsion x Y₀ X₀ :=
  cov.isCovariantDerivativeOn.torsion_antisymm ..
/-
**CovariantDerivative.torsion_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `CovariantDe
rivative`。
形式化陈述：torsion_eq_zero_iff : cov.torsion = 0 ↔ forall {X Y x}, MDiffAt (T% X) x -
> MDiffAt (T% Y) x -> cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CovariantDerivative.torsion_apply`：torsion_apply (hX : MDiffAt (T% X) x)
 (hY : MDiffAt (T% Y) x) : cov.torsion x (X x) (Y x) = cov Y x (X x) - cov X x (
Y x) - mlieBracket I X …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用引理 `CovariantDerivative.torsion_apply_eq_extend`：torsion_apply_eq_extend (X₀
 Y₀ : TangentSpace I x) : cov.torsion x X₀ Y₀ = cov (extend E Y₀) x (extend E X₀
 x) - cov (extend E X₀) x (extend…
· 使用引理 `FiberBundle.mdifferentiableAt_extend`：mdifferentiableAt_extend {x : M} (
σ₀ : V x) : MDiffAt (T% (extend F σ₀)) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma torsion_eq_zero_iff : cov.torsion = 0 ↔
    ∀ {X Y x}, MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x := by
  constructor
  · intro h X Y x hX hY
    replace h := congr($h x (X x) (Y x))
    rw [cov.torsion_apply hX hY] at h
    simpa [sub_eq_iff_eq_add'] using h
  · intro h
    ext x u v
    rw [torsion_apply_eq_extend, h]
    · simp
    · apply mdifferentiableAt_extend
    · apply mdifferentiableAt_extend

end CovariantDerivative

