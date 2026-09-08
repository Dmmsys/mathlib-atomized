/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.Notation

/-!
# Vector fields in manifolds

We study functions of the form `V : Π (x : M), TangentSpace I x` on a manifold, i.e.,
vector fields.

We define the pullback of a vector field under a map, as
`VectorField.mpullback I I' f V x := (mfderiv I I' f x).inverse (V (f x))`
(together with the same notion within a set). Note that the pullback uses the junk-value pattern:
if the derivative of the map is not invertible, then pullback is given the junk value zero.

See `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean` for the Lie bracket of two vector
fields.

These definitions are given in the `VectorField` namespace because pullbacks, Lie brackets,
and so on, are notions that make sense in a variety of contexts.
We also prefix the notions with `m` to distinguish the manifold notions from the vector space
notions.

For notions that come naturally in other namespaces for dot notation, we specify `vectorField` in
the name to lift ambiguities. For instance, the fact that the Lie bracket of two smooth vector
fields is smooth is `ContMDiffAt.mlieBracket_vectorField`.

Note that a smoothness assumption for a vector field is written by seeing the vector field as
a function from `M` to its tangent bundle through a coercion, as in:
`MDifferentiableWithinAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) s x`
(or `MDiffAt[s] (T% V) x`, for short).
-/

@[expose] public section

open Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section

/- We work in the `VectorField` namespace because pullbacks, Lie brackets, and so on, are notions
that make sense in a variety of contexts. We also prefix the notions with `m` to distinguish the
manifold notions from the vector space notions. For instance, the Lie bracket of two vector
fields in a manifold is denoted with `VectorField.mlieBracket I V W x`, where `I` is the relevant
model with corners, `V W : Π (x : M), TangentSpace I x` are the vector fields, and `x : M` is
the basepoint.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f : M → M'} {s t : Set M} {x x₀ : M}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} [n.AtLeastTwo] [IsManifold I (minSmoothness 𝕜 (ofNat(n))) M] :
    IsManifold I (ofNat(n)) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 n) le_minSmoothness
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsManifold I (minSmoothness 𝕜 1) M] :
    IsManifold I 1 M :=
  IsManifold.of_le (n := minSmoothness 𝕜 1) le_minSmoothness
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsManifold I (minSmoothness 𝕜 3) M] :
    IsManifold I (minSmoothness 𝕜 2) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 3) (minSmoothness_monotone (by norm_cast))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsManifold I (minSmoothness 𝕜 2) M] :
    IsManifold I (minSmoothness 𝕜 1) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 2) (minSmoothness_monotone (by norm_cast))

namespace VectorField

section Pullback

/-! ### Pullback of vector fields in manifolds -/

open ContinuousLinearMap

variable {V W V₁ W₁ : Π (x : M'), TangentSpace I' x}
variable {c : 𝕜} {m n : ℕ∞ω} {t : Set M'} {y₀ : M'}

variable (I I') in
/-- The pullback of a vector field under a map between manifolds, within a set `s`. If the
derivative of the map within `s` is not invertible, then pullback is given the junk value zero. -/
/-
**VectorField.mpullbackWithin** 是 Mathlib 中的一个定义，位于命名空间 `VectorField`。
形式化陈述：mpullbackWithin (f : M -> M') (V : Π (x : M'), TangentSpace I' x) (s : Set
 M) (x : M) : TangentSpace I x
参数：f : M -> M'；V : Π (x : M'), TangentSpace I' x；s : Set M；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a vector field under a map between manifolds, within a set `s`. 
If the
derivative of the map within `s` is not invertible, then pullback is given the j
unk value zero.
-/
def mpullbackWithin (f : M → M') (V : Π (x : M'), TangentSpace I' x) (s : Set M) (x : M) :
    TangentSpace I x :=
  (mfderiv[s] f x).inverse (V (f x))

variable (I I') in
/-- The pullback of a vector field under a map between manifolds. If the derivative of the map is
not invertible, then pullback is given the junk value zero. -/
/-
**VectorField.mpullback** 是 Mathlib 中的一个定义，位于命名空间 `VectorField`。
形式化陈述：mpullback (f : M -> M') (V : Π (x : M'), TangentSpace I' x) (x : M) : Tang
entSpace I x
参数：f : M -> M'；V : Π (x : M'), TangentSpace I' x；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a vector field under a map between manifolds. If the derivative 
of the map is
not invertible, then pullback is given the junk value zero.
-/
def mpullback (f : M → M') (V : Π (x : M'), TangentSpace I' x) (x : M) :
    TangentSpace I x :=
  (mfderiv% f x).inverse (V (f x))
/-
**VectorField.mpullbackWithin_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullbackWithin_apply : mpullbackWithin I I' f V s x = (mfderiv[s] f x).in
verse (V (f x))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mpullbackWithin_apply :
    mpullbackWithin I I' f V s x = (mfderiv[s] f x).inverse (V (f x)) := rfl
/-
**VectorField.mpullbackWithin_const_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Vector
Field`。
形式化陈述：mpullbackWithin_const_smul_apply : mpullbackWithin I I' f (c • V) s x = c 
• mpullbackWithin I I' f V s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullbackWithin_const_smul_apply :
    mpullbackWithin I I' f (c • V) s x = c • mpullbackWithin I I' f V s x := by
  simp [mpullbackWithin_apply]
/-
**VectorField.mpullbackWithin_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`
。
形式化陈述：mpullbackWithin_smul_apply {g : M' -> 𝕜} : mpullbackWithin I I' f (g • V) 
s x = g (f x) • mpullbackWithin I I' f V s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullbackWithin_smul_apply {g : M' → 𝕜} :
    mpullbackWithin I I' f (g • V) s x = g (f x) • mpullbackWithin I I' f V s x := by
  simp [mpullbackWithin_apply]
/-
**VectorField.mpullbackWithin_const_smul** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`
。
形式化陈述：mpullbackWithin_const_smul : mpullbackWithin I I' f (c • V) s = c • mpullb
ackWithin I I' f V s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullbackWithin_const_smul :
    mpullbackWithin I I' f (c • V) s = c • mpullbackWithin I I' f V s := by
  ext x
  simp [mpullbackWithin_apply]
/-
**VectorField.mpullbackWithin_smul** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullbackWithin_smul {g : M' -> 𝕜} : mpullbackWithin I I' f (g • V) s = (g
 ∘ f) • mpullbackWithin I I' f V s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullbackWithin_smul {g : M' → 𝕜} :
    mpullbackWithin I I' f (g • V) s = (g ∘ f) • mpullbackWithin I I' f V s := by
  ext; simp [mpullbackWithin_apply]
/-
**VectorField.mpullbackWithin_add_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullbackWithin_add_apply : mpullbackWithin I I' f (V + V₁) s x = mpullbac
kWithin I I' f V s x + mpullbackWithin I I' f V₁ s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullbackWithin_add_apply :
    mpullbackWithin I I' f (V + V₁) s x =
      mpullbackWithin I I' f V s x + mpullbackWithin I I' f V₁ s x := by
  simp [mpullbackWithin_apply]
/-
**VectorField.mpullbackWithin_add** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullbackWithin_add : mpullbackWithin I I' f (V + V₁) s = mpullbackWithin 
I I' f V s + mpullbackWithin I I' f V₁ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullbackWithin_add :
    mpullbackWithin I I' f (V + V₁) s =
      mpullbackWithin I I' f V s + mpullbackWithin I I' f V₁ s := by
  ext x
  simp [mpullbackWithin_apply]

@[simp]
/-
**VectorField.mpullbackWithin_zero** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullbackWithin_zero : mpullbackWithin I I' f 0 s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullbackWithin_zero : mpullbackWithin I I' f 0 s = 0 := by
  ext x
  simp [mpullbackWithin_apply]
/-
**VectorField.mpullbackWithin_neg_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullbackWithin_neg_apply : mpullbackWithin I I' f (-V) s x = - mpullbackW
ithin I I' f V s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullbackWithin_neg_apply :
    mpullbackWithin I I' f (-V) s x = - mpullbackWithin I I' f V s x := by
  simp [mpullbackWithin_apply]
/-
**VectorField.mpullbackWithin_neg** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullbackWithin_neg : mpullbackWithin I I' f (-V) s = - mpullbackWithin I 
I' f V s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullbackWithin_neg :
    mpullbackWithin I I' f (-V) s = - mpullbackWithin I I' f V s := by
  ext x
  simp [mpullbackWithin_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mpullbackWithin_id** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullbackWithin_id {V : Π (x : M), TangentSpace I x} (h : UniqueMDiffAt[s]
 x) : mpullbackWithin I I id V s x = V x
参数：x : M；h : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_id`：mfderivWithin_id (hxs : UniqueMDiffAt[s] x) : mfderiv[
s] (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x)
· 使用定理 `ContinuousLinearMap.inverse_id`：∀ {R : Type u_1} {M : Type u_2} [inst : 
TopologicalSpace M] [inst_1 : Semiring R] [inst_2 : AddCommMonoid M]   [inst_3 :
 _root_.Module R M],…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullbackWithin_id {V : Π (x : M), TangentSpace I x} (h : UniqueMDiffAt[s] x) :
    mpullbackWithin I I id V s x = V x := by
  simp [mpullbackWithin_apply, mfderivWithin_id h]
/-
**VectorField.mpullback_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_apply : mpullback I I' f V x = (mfderiv% f x).inverse (V (f x))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mpullback_apply :
    mpullback I I' f V x = (mfderiv% f x).inverse (V (f x)) := rfl
/-
**VectorField.mpullback_const_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`
。
形式化陈述：mpullback_const_smul_apply : mpullback I I' f (c • V) x = c • mpullback I 
I' f V x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullback_const_smul_apply :
    mpullback I I' f (c • V) x = c • mpullback I I' f V x := by
  simp [mpullback]
/-
**VectorField.mpullback_const_smul** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_const_smul : mpullback I I' f (c • V) = c • mpullback I I' f V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullback_const_smul :
    mpullback I I' f (c • V) = c • mpullback I I' f V := by
  ext x
  simp [mpullback_apply]
/-
**VectorField.mpullback_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_smul_apply {g : M' -> 𝕜} : mpullback I I' f (g • V) x = g (f x) 
• mpullback I I' f V x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullback_smul_apply {g : M' → 𝕜} :
    mpullback I I' f (g • V) x = g (f x) • mpullback I I' f V x := by
  simp [mpullback]
/-
**VectorField.mpullback_smul** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_smul {g : M' -> 𝕜} : mpullback I I' f (g • V) = (g ∘ f) • mpullb
ack I I' f V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullback_smul {g : M' → 𝕜} :
    mpullback I I' f (g • V) = (g ∘ f) • mpullback I I' f V := by
  ext x
  simp [mpullback_apply]
/-
**VectorField.mpullback_add_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_add_apply : mpullback I I' f (V + V₁) x = mpullback I I' f V x +
 mpullback I I' f V₁ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullback_add_apply :
    mpullback I I' f (V + V₁) x = mpullback I I' f V x + mpullback I I' f V₁ x := by
  simp [mpullback_apply]
/-
**VectorField.mpullback_add** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_add : mpullback I I' f (V + V₁) = mpullback I I' f V + mpullback
 I I' f V₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullback_add :
    mpullback I I' f (V + V₁) = mpullback I I' f V + mpullback I I' f V₁ := by
  ext x
  simp [mpullback_apply]
/-
**VectorField.mpullback_neg_apply** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_neg_apply : mpullback I I' f (-V) x = - mpullback I I' f V x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullback_neg_apply :
    mpullback I I' f (-V) x = - mpullback I I' f V x := by
  simp [mpullback_apply]
/-
**VectorField.mpullback_neg** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_neg : mpullback I I' f (-V) = - mpullback I I' f V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullback_neg :
    mpullback I I' f (-V) = - mpullback I I' f V := by
  ext x
  simp [mpullback_apply]
/-
**VectorField.mpullbackWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1
 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCommGroup E] [inst_3 
: NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {H' : Type u_5} [inst_6 : Topological
Space H']   {E' : Type u_6} [inst_7 : NormedAddCommGroup E'] [inst_8 : NormedSpa
ce 𝕜 E'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'}   {V : (x : M') → TangentS
pace I' x}, VectorField.mpullbackWithin I I' f V Set.univ = VectorField.mpullbac
k I I' f V
参数：x : M'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mpullbackWithin_univ : mpullbackWithin I I' f V univ = mpullback I I' f V := by
  ext x
  simp [mpullback_apply, mpullbackWithin_apply]

@[simp]
/-
**VectorField.mpullback_zero** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_zero : mpullback I I' f 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mpullbackWithin_zero`：mpullbackWithin_zero : mpullbackWithin
 I I' f 0 s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullback_zero : mpullback I I' f 0 = 0 := by simp [← mpullbackWithin_univ]
/-
**VectorField.mpullbackWithin_eq_pullbackWithin** 是 Mathlib 中的一个引理，位于命名空间 `Vecto
rField`。
形式化陈述：mpullbackWithin_eq_pullbackWithin {f : E -> E'} {V : E' -> E'} {s : Set E}
 : mpullbackWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f V s = pullbackWithin 𝕜 f V s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_eq_fderivWithin`：mfderivWithin_eq_fderivWithin : mfderiv[s
] f x = fderivWithin 𝕜 f s x
-/
lemma mpullbackWithin_eq_pullbackWithin {f : E → E'} {V : E' → E'} {s : Set E} :
    mpullbackWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f V s = pullbackWithin 𝕜 f V s := by
  ext x
  simp only [mpullbackWithin, mfderivWithin_eq_fderivWithin, pullbackWithin]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mpullback_eq_pullback** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：mpullback_eq_pullback {f : E -> E'} {V : E' -> E'} : mpullback 𝓘(𝕜, E) 𝓘(𝕜
, E') f V = pullback 𝕜 f V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mpullbackWithin_eq_pullbackWithin`：mpullbackWithin_eq_pullba
ckWithin {f : E -> E'} {V : E' -> E'} {s : Set E} : mpullbackWithin 𝓘(𝕜, E) 𝓘(𝕜,
 E') f V s = pullbackWithin 𝕜 f V s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mpullback_eq_pullback {f : E → E'} {V : E' → E'} :
    mpullback 𝓘(𝕜, E) 𝓘(𝕜, E') f V = pullback 𝕜 f V := by
  simp only [← mpullbackWithin_univ, ← pullbackWithin_univ, mpullbackWithin_eq_pullbackWithin]

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mpullback_id** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1
 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCommGroup E] [inst_3 
: NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {V : (x : M) → TangentSpace I x},   V
ectorField.mpullback I I id V = V
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_id`：mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (
TangentSpace% x)
· 使用定理 `ContinuousLinearMap.inverse_id`：∀ {R : Type u_1} {M : Type u_2} [inst : 
TopologicalSpace M] [inst_1 : Semiring R] [inst_2 : AddCommMonoid M]   [inst_3 :
 _root_.Module R M],…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mpullback_id {V : Π (x : M), TangentSpace I x} : mpullback I I id V = V := by
  ext x
  simp [mpullback]
/-
**VectorField.mpullbackWithin_comp_of_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorFiel
d`。
形式化陈述：mpullbackWithin_comp_of_left {g : M' -> M''} {f : M -> M'} {V : Π (x : M''
), TangentSpace I'' x} {s : Set M} {t : Set M'} {x₀ : M} (hf : MDiffAt[s] f x₀) 
(h : Set.MapsTo f s t) (hu : UniqueMDiffAt[s] x₀) (hg' : (mfderiv[t] g (f x₀)).I
sInvertible) : mpullbackWithin I I'' (g ∘ f) V s x₀ = mpullbackWithin I I' f (mp
ullbackWithin I' I'' g V t) s x₀
参数：x : M''；hf : MDiffAt[s] f x₀；h : Set.MapsTo f s t；hu : UniqueMDiffAt[s] x₀；hg
' : (mfderiv[t] g (f x₀)).IsInvertible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableWithinAt_of_isInvertible_mfderivWithin`：mdifferentiableWi
thinAt_of_isInvertible_mfderivWithin (hf : (mfderiv[s] f x).IsInvertible) : MDif
fAt[s] f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_comp`：mfderivWithin_comp (hg : MDiffAt[u] g (f x)) (hf : M
DiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] 
(g ∘ f) …
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_left`：∀ {R : Type
 u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : TopologicalSpace M]
   [inst_1 : TopologicalSpace M₂] [inst_2 : Topol…
-/
lemma mpullbackWithin_comp_of_left
    {g : M' → M''} {f : M → M'} {V : Π (x : M''), TangentSpace I'' x} {s : Set M} {t : Set M'}
    {x₀ : M} (hf : MDiffAt[s] f x₀) (h : Set.MapsTo f s t)
    (hu : UniqueMDiffAt[s] x₀) (hg' : (mfderiv[t] g (f x₀)).IsInvertible) :
    mpullbackWithin I I'' (g ∘ f) V s x₀ =
      mpullbackWithin I I' f (mpullbackWithin I' I'' g V t) s x₀ := by
  simp only [mpullbackWithin]
  have hg : MDifferentiableWithinAt I' I'' g t (f x₀) :=
    mdifferentiableWithinAt_of_isInvertible_mfderivWithin hg'
  rw [mfderivWithin_comp _ hg hf h hu, Function.comp_apply,
    IsInvertible.inverse_comp_apply_of_left hg']

set_option backward.isDefEq.respectTransparency false in
/-
**VectorField.mpullbackWithin_comp_of_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorFie
ld`。
形式化陈述：mpullbackWithin_comp_of_right {g : M' -> M''} {f : M -> M'} {V : Π (x : M'
'), TangentSpace I'' x} {s : Set M} {t : Set M'} {x₀ : M} (hg : MDiffAt[t] g (f 
x₀)) (h : Set.MapsTo f s t) (hu : UniqueMDiffAt[s] x₀) (hf' : (mfderiv[s] f x₀).
IsInvertible) : mpullbackWithin I I'' (g ∘ f) V s x₀ = mpullbackWithin I I' f (m
pullbackWithin I' I'' g V t) s x₀
参数：x : M''；hg : MDiffAt[t] g (f x₀)；h : Set.MapsTo f s t；hu : UniqueMDiffAt[s] x
₀；hf' : (mfderiv[s] f x₀).IsInvertible。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableWithinAt_of_isInvertible_mfderivWithin`：mdifferentiableWi
thinAt_of_isInvertible_mfderivWithin (hf : (mfderiv[s] f x).IsInvertible) : MDif
fAt[s] f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_comp`：mfderivWithin_comp (hg : MDiffAt[u] g (f x)) (hf : M
DiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] 
(g ∘ f) …
· 使用定理 `ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right`：∀ {R : Typ
e u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : TopologicalSpace M
]   [inst_1 : TopologicalSpace M₂] [inst_2 : Topol…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma mpullbackWithin_comp_of_right
    {g : M' → M''} {f : M → M'} {V : Π (x : M''), TangentSpace I'' x} {s : Set M} {t : Set M'}
    {x₀ : M} (hg : MDiffAt[t] g (f x₀)) (h : Set.MapsTo f s t)
    (hu : UniqueMDiffAt[s] x₀) (hf' : (mfderiv[s] f x₀).IsInvertible) :
    mpullbackWithin I I'' (g ∘ f) V s x₀ =
      mpullbackWithin I I' f (mpullbackWithin I' I'' g V t) s x₀ := by
  simp only [mpullbackWithin]
  have hf : MDifferentiableWithinAt I I' f s x₀ :=
    mdifferentiableWithinAt_of_isInvertible_mfderivWithin hf'
  rw [mfderivWithin_comp _ hg hf h hu, IsInvertible.inverse_comp_apply_of_right hf',
    Function.comp_apply]


/-! ### Regularity of pullback of vector fields

In this paragraph, we assume that the model space is complete, to ensure that the set of invertible
linear maps is open and that inversion is a smooth map there. Otherwise, the pullback of vector
fields could behave wildly, even at points where the derivative of the map is invertible.
-/

section MDifferentiability

variable [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E]

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point. -/
/-
**VectorField._root_.MDifferentiableWithinAt.mpullbackWithin_vectorField_inter**
 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` i
s
differentiable. Version within a set at a point.
-/
protected lemma _root_.MDifferentiableWithinAt.mpullbackWithin_vectorField_inter
    (hV : MDiffAt[t] (T% V) (f x₀)) (hf : CMDiffAt[s] n f x₀) (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : 2 ≤ n) :
    MDiffAt[s ∩ f ⁻¹' t] (T% (mpullbackWithin I I' f V s)) x₀ := by
  /- We want to apply the theorem `MDifferentiableWithinAt.clm_apply_of_inCoordinates`,
  stating that applying linear maps to vector fields gives a smooth result when the linear map and
  the vector field are smooth. This theorem is general, we will apply it to
  `b₁ = f`, `b₂ = id`, `v = V ∘ f`, `ϕ = fun x ↦ (mfderivWithin I I' f s x).inverse` -/
  let b₁ := f
  let b₂ : M → M := id
  let v : Π (x : M), TangentSpace I' (f x) := V ∘ f
  let ϕ : Π (x : M), TangentSpace I' (f x) →L[𝕜] TangentSpace I x :=
    fun x ↦ (mfderiv[s] f x).inverse
  have hv : MDifferentiableWithinAt I I'.tangent
      (fun x ↦ (v x : TangentBundle I' M')) (s ∩ f ⁻¹' t) x₀ := by
    apply hV.comp x₀ ((hf.mdifferentiableWithinAt (by positivity)).mono inter_subset_left)
    exact MapsTo.mono_left (mapsTo_preimage _ _) inter_subset_right
  /- The only nontrivial fact, from which the conclusion follows, is
  that `ϕ` depends smoothly on `x`. -/
  suffices hϕ : MDifferentiableWithinAt I 𝓘(𝕜, E' →L[𝕜] E)
      (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E' (TangentSpace I' (M := M')) E (TangentSpace I (M := M))
        (b₁ x₀) (b₁ x) (b₂ x₀) (b₂ x) (ϕ x)) s x₀ from
    MDifferentiableWithinAt.clm_apply_of_inCoordinates (hϕ.mono inter_subset_left)
      hv mdifferentiableWithinAt_id
  /- To prove that `ϕ` depends smoothly on `x`, we use that the derivative depends smoothly on `x`
  (this is `ContMDiffWithinAt.mfderivWithin_const`), and that taking the inverse is a smooth
  operation at an invertible map. -/
  -- the derivative in coordinates depends smoothly on the point
  have : MDifferentiableWithinAt I 𝓘(𝕜, E →L[𝕜] E')
      (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderiv[s] f x)) s x₀ :=
    ((hf.of_le hmn).mfderivWithin_const le_rfl hx₀ hs).mdifferentiableWithinAt one_ne_zero
  -- therefore, its inverse in coordinates also depends smoothly on the point
  have : MDiffAt[s]
      (ContinuousLinearMap.inverse ∘ (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderiv[s] f x))) x₀ := by
    apply MDifferentiableAt.comp_mdifferentiableWithinAt _ _ this
    apply ContMDiffAt.mdifferentiableAt _ one_ne_zero
    apply ContDiffAt.contMDiffAt
    apply IsInvertible.contDiffAt_map_inverse
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
      (FiberBundle.mem_baseSet_trivializationAt' (f x₀))]
    exact isInvertible_equiv.comp (hf'.comp isInvertible_equiv)
  -- the inverse in coordinates coincides with the in-coordinate version of the inverse,
  -- therefore the previous point gives the conclusion
  apply this.congr_of_eventuallyEq_of_mem _ hx₀
  have A : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝[s] x₀ := by
    apply nhdsWithin_le_nhds
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  have B : f ⁻¹' (trivializationAt E' (TangentSpace I') (f x₀)).baseSet ∈ 𝓝[s] x₀ := by
    apply hf.continuousWithinAt.preimage_mem_nhdsWithin
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  filter_upwards [A, B] with x hx h'x
  simp only [Function.comp_apply]
  rw [inCoordinates_eq hx h'x, inCoordinates_eq h'x (by exact hx)]
  simp only [inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm, ϕ]
  rfl
/-
**VectorField._root_.MDifferentiableWithinAt.mpullbackWithin_vectorField_inter_o
f_eq** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MDifferentiableWithinAt.mpullbackWithin_vectorField_inter_of_eq
    (hV : MDiffAt[t] (T% V) y₀) (hf : CMDiffAt[s] n f x₀)
    (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : 2 ≤ n) (h : y₀ = f x₀) :
    MDiffAt[s ∩ f ⁻¹' t] (T% (mpullbackWithin I I' f V s)) x₀ := by
  subst h
  exact hV.mpullbackWithin_vectorField_inter hf hf' hx₀ hs hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version on a set. -/
/-
**VectorField._root_.MDifferentiableOn.mpullbackWithin_vectorField_inter** 是 Mat
hlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` i
s
differentiable. Version on a set.
-/
protected lemma _root_.MDifferentiableOn.mpullbackWithin_vectorField_inter
    (hV : MDiff[t] (T% V)) (hf : CMDiff[s] n f)
    (hf' : ∀ x ∈ s ∩ f ⁻¹' t, (mfderiv[s] f x).IsInvertible)
    (hs : UniqueMDiff[s]) (hmn : 2 ≤ n) :
    MDiff[(s ∩ f ⁻¹' t)] (T% (mpullbackWithin I I' f V s)) :=
  fun _ hx₀ ↦ MDifferentiableWithinAt.mpullbackWithin_vectorField_inter
    (hV _ hx₀.2) (hf _ hx₀.1) (hf' _ hx₀) hx₀.1 hs hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point, but with full pullback. -/
/-
**VectorField._root_.MDifferentiableWithinAt.mpullback_vectorField_preimage** 是 
Mathlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` i
s
differentiable. Version within a set at a point, but with full pullback.
-/
protected lemma _root_.MDifferentiableWithinAt.mpullback_vectorField_preimage
    (hV : MDiffAt[t] (T% V) (f x₀)) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : 2 ≤ n) :
    MDiffAt[f ⁻¹' t] (T% (mpullback I I' f V)) x₀ := by
  simp only [← contMDiffWithinAt_univ, ← mfderivWithin_univ, ← mpullbackWithin_univ] at hV hf hf' ⊢
  simpa using hV.mpullbackWithin_vectorField_inter hf hf' (mem_univ _) uniqueMDiffOn_univ hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point, but with full pullback. -/
/-
**VectorField._root_.MDifferentiableWithinAt.mpullback_vectorField_preimage_of_e
q** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` i
s
differentiable. Version within a set at a point, but with full pullback.
-/
protected lemma _root_.MDifferentiableWithinAt.mpullback_vectorField_preimage_of_eq
    (hV : MDiffAt[t] (T% V) y₀) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : 2 ≤ n) (hy₀ : y₀ = f x₀) :
    MDiffAt[f ⁻¹' t] (T% (mpullback I I' f V)) x₀ := by
  subst hy₀
  exact hV.mpullback_vectorField_preimage hf hf' hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version on a set, but with full pullback -/
/-
**VectorField._root_.MDifferentiableOn.mpullback_vectorField_preimage** 是 Mathli
b 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` i
s
differentiable. Version on a set, but with full pullback
-/
protected lemma _root_.MDifferentiableOn.mpullback_vectorField_preimage
    (hV : MDiff[t] (T% V)) (hf : CMDiff n f)
    (hf' : ∀ x ∈ f ⁻¹' t, (mfderiv% f x).IsInvertible)
    (hmn : 2 ≤ n) :
    MDiff[f ⁻¹' t] (T% (mpullback I I' f V)) :=
  fun x₀ hx₀ ↦ MDifferentiableWithinAt.mpullback_vectorField_preimage
    (hV _ hx₀) (hf x₀) (hf' _ hx₀) hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version at a point. -/
/-
**VectorField._root_.MDifferentiableAt.mpullback_vectorField** 是 Mathlib 中的一个引理，
位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` i
s
differentiable. Version at a point.
-/
protected lemma _root_.MDifferentiableAt.mpullback_vectorField
    (hV : MDiffAt (T% V) (f x₀)) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : 2 ≤ n) :
    MDiffAt (T% (mpullback I I' f V)) x₀ := by
  simpa using! MDifferentiableWithinAt.mpullback_vectorField_preimage hV hf hf' hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. -/
/-
**VectorField._root_.MDifferentiable.mpullback_vectorField** 是 Mathlib 中的一个引理，位于
命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` i
s
differentiable.
-/
protected lemma _root_.MDifferentiable.mpullback_vectorField
    (hV : MDiff (T% V)) (hf : CMDiff n f) (hf' : ∀ x, (mfderiv% f x).IsInvertible) (hmn : 2 ≤ n) :
    MDiff (T% (mpullback I I' f V)) :=
  fun x ↦ MDifferentiableAt.mpullback_vectorField (hV (f x)) (hf x) (hf' x) hmn

end MDifferentiability


section ContMDiff

variable [CompleteSpace E] [IsManifold I 1 M] [IsManifold I' 1 M']

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
`m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullbackWithin_vectorField_inter** 是 Mat
hlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
`m + 1 ≤ n` is `C^m`.
Version within a set at a point.
-/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_inter
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt[s] n f x₀)
    (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) :
    CMDiffAt[s ∩ f ⁻¹' t] m (T% (mpullbackWithin I I' f V s)) x₀ := by
  /- We want to apply the theorem `ContMDiffWithinAt.clm_apply_of_inCoordinates`, stating
  that applying linear maps to vector fields gives a smooth result when the linear map and the
  vector field are smooth. This theorem is general, we will apply it to
  `b₁ = f`, `b₂ = id`, `v = V ∘ f`, `ϕ = fun x ↦ (mfderivWithin I I' f s x).inverse` -/
  let b₁ := f
  let b₂ : M → M := id
  let v : Π (x : M), TangentSpace I' (f x) := V ∘ f
  let ϕ : Π (x : M), TangentSpace I' (f x) →L[𝕜] TangentSpace I x :=
    fun x ↦ (mfderiv[s] f x).inverse
  have hv : ContMDiffWithinAt I I'.tangent m
      (fun x ↦ (v x : TangentBundle I' M')) (s ∩ f ⁻¹' t) x₀ := by
    apply hV.comp x₀ ((hf.of_le (le_trans (le_self_add) hmn)).mono inter_subset_left)
    exact MapsTo.mono_left (mapsTo_preimage _ _) inter_subset_right
  /- The only nontrivial fact, from which the conclusion follows, is
  that `ϕ` depends smoothly on `x`. -/
  suffices hϕ : CMDiffAt[s] m (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E' (TangentSpace I' (M := M')) E (TangentSpace I (M := M))
        (b₁ x₀) (b₁ x) (b₂ x₀) (b₂ x) (ϕ x)) x₀ from
    ContMDiffWithinAt.clm_apply_of_inCoordinates (hϕ.mono inter_subset_left) hv contMDiffWithinAt_id
  /- To prove that `ϕ` depends smoothly on `x`, we use that the derivative depends smoothly on `x`
  (this is `ContMDiffWithinAt.mfderivWithin_const`), and that taking the inverse is a smooth
  operation at an invertible map. -/
  -- the derivative in coordinates depends smoothly on the point
  have : CMDiffAt[s] m (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderiv[s] f x)) x₀ :=
    hf.mfderivWithin_const hmn hx₀ hs
  -- therefore, its inverse in coordinates also depends smoothly on the point
  have : CMDiffAt[s] m
      (ContinuousLinearMap.inverse ∘ (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderiv[s] f x))) x₀ := by
    apply ContMDiffAt.comp_contMDiffWithinAt _ _ this
    apply ContDiffAt.contMDiffAt
    apply IsInvertible.contDiffAt_map_inverse
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
      (FiberBundle.mem_baseSet_trivializationAt' (f x₀))]
    exact isInvertible_equiv.comp (hf'.comp isInvertible_equiv)
  -- the inverse in coordinates coincides with the in-coordinate version of the inverse,
  -- therefore the previous point gives the conclusion
  apply this.congr_of_eventuallyEq_of_mem _ hx₀
  have A : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝[s] x₀ := by
    apply nhdsWithin_le_nhds
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  have B : f ⁻¹' (trivializationAt E' (TangentSpace I') (f x₀)).baseSet ∈ 𝓝[s] x₀ := by
    apply hf.continuousWithinAt.preimage_mem_nhdsWithin
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  filter_upwards [A, B] with x hx h'x
  simp only [Function.comp_apply]
  rw [inCoordinates_eq hx h'x, inCoordinates_eq h'x (by exact hx)]
  simp only [inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm, ϕ]
  rfl
/-
**VectorField._root_.ContMDiffWithinAt.mpullbackWithin_vectorField_inter_of_eq**
 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_inter_of_eq
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt[s] n f x₀) (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (h : f x₀ = y₀) :
    CMDiffAt[s ∩ f ⁻¹' t] m (T% (mpullbackWithin I I' f V s)) x₀ := by
  subst h
  exact ContMDiffWithinAt.mpullbackWithin_vectorField_inter hV hf hf' hx₀ hs hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem** 是 Ma
thlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point.
-/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt[s] n f x₀)
    (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀) :
    CMDiffAt[s] m (T% (mpullbackWithin I I' f V s)) x₀ := by
  apply (ContMDiffWithinAt.mpullbackWithin_vectorField_inter
    hV hf hf' hx₀ hs hmn).mono_of_mem_nhdsWithin
  exact Filter.inter_mem self_mem_nhdsWithin hst

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem_of_eq*
* 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point.
-/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem_of_eq
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt[s] n f x₀) (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hy₀ : f x₀ = y₀) :
    CMDiffAt[s] m (T% (mpullbackWithin I I' f V s)) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem hV hf hf' hx₀ hs hmn hst

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullbackWithin_vectorField** 是 Mathlib 中
的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point.
-/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt[s] n f x₀)
    (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (hst : MapsTo f s t) :
    CMDiffAt[s] m (T% (mpullbackWithin I I' f V s)) x₀ :=
  ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem hV hf hf' hx₀ hs hmn
    hst.preimage_mem_nhdsWithin

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq** 是 Mat
hlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point.
-/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt[s] n f x₀) (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (hst : MapsTo f s t) (h : f x₀ = y₀) :
    CMDiffAt[s] m (T% (mpullbackWithin I I' f V s)) x₀ := by
  subst h
  exact ContMDiffWithinAt.mpullbackWithin_vectorField hV hf hf' hx₀ hs hmn hst

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, with a set used for the pullback possibly larger. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullbackWithin_vectorField'** 是 Mathlib 
中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, with a set used for the pullback possibly large
r.
-/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField' {u : Set M}
    (hV : CMDiffAt[t] m (T% V) (f x₀))
    (hf : CMDiffAt[u] n f x₀) (hf' : (mfderiv[u] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (hu : s ⊆ u) :
    CMDiffAt[s] m (T% (mpullbackWithin I I' f V u)) x₀ := by
  have hn : 1 ≤ n := le_trans (by simp) hmn
  have hh : (mfderiv[s] f x₀).IsInvertible := by
    convert! hf' using 1
    exact (hf.mdifferentiableWithinAt <| by positivity).mfderivWithin_mono (hs _ hx₀) hu
  apply (hV.mpullbackWithin_vectorField_of_mem (hf.mono hu) hh hx₀ hs hmn
    hst).congr_of_eventuallyEq_of_mem _ hx₀
  have Y := (contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin (by simp)).1 (hf.of_le hn)
  simp_rw [insert_eq_of_mem (hu hx₀)] at Y
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_mono _ hu Y] with y hy h'y
  simp only [mpullbackWithin, Bundle.TotalSpace.mk_inj]
  rw [MDifferentiableWithinAt.mfderivWithin_mono (h'y.mdifferentiableWithinAt one_ne_zero)
    (hs _ hy) hu]

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, with a set used for the pullback possibly larger. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq'** 是 Ma
thlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, with a set used for the pullback possibly large
r.
-/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq' {u : Set M}
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt[u] n f x₀) (hf' : (mfderiv[u] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hu : s ⊆ u) (hy₀ : f x₀ = y₀) :
    CMDiffAt[s] m (T% (mpullbackWithin I I' f V u)) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullbackWithin_vectorField' hV hf hf' hx₀ hs hmn hst hu

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version on a set. -/
/-
**VectorField._root_.ContMDiffOn.mpullbackWithin_vectorField_inter** 是 Mathlib 中
的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version on a set.
-/
protected lemma _root_.ContMDiffOn.mpullbackWithin_vectorField_inter
    (hV : CMDiff[t] m (T% V)) (hf : CMDiff[s] n f)
    (hf' : ∀ x ∈ s ∩ f ⁻¹' t, (mfderiv[s] f x).IsInvertible)
    (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) :
    CMDiff[s ∩ f ⁻¹' t] m (T% (mpullbackWithin I I' f V s)) :=
  fun _ hx₀ ↦ ContMDiffWithinAt.mpullbackWithin_vectorField_inter
    (hV _ hx₀.2) (hf _ hx₀.1) (hf' _ hx₀) hx₀.1 hs hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullback_vectorField_preimage** 是 Mathli
b 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback.
-/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_preimage
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : m + 1 ≤ n) :
    CMDiffAt[f ⁻¹' t] m (T% (mpullback I I' f V)) x₀ := by
  simp only [← contMDiffWithinAt_univ, ← mfderivWithin_univ, ← mpullbackWithin_univ] at hV hf hf' ⊢
  simpa using hV.mpullbackWithin_vectorField_inter hf hf' (mem_univ _) uniqueMDiffOn_univ hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullback_vectorField_preimage_of_eq** 是 
Mathlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback.
-/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_preimage_of_eq
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : m + 1 ≤ n) (hy₀ : y₀ = f x₀) :
    CMDiffAt[f ⁻¹' t] m (T% (mpullback I I' f V)) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin**
 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback.
-/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀) :
    CMDiffAt[s] m (T% (mpullback I I' f V)) x₀ :=
  (ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn).mono_of_mem_nhdsWithin hst

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
/-
**VectorField._root_.ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin_o
f_eq** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback.
-/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin_of_eq
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (hy₀ : y₀ = f x₀) :
    CMDiffAt[s] m (T% (mpullback I I' f V)) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin hV hf hf' hmn hst

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version on a set, but with full pullback -/
/-
**VectorField._root_.ContMDiffOn.mpullback_vectorField_preimage** 是 Mathlib 中的一个
引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version on a set, but with full pullback
-/
protected lemma _root_.ContMDiffOn.mpullback_vectorField_preimage
    (hV : CMDiff[t] m (T% V)) (hf : CMDiff n f)
    (hf' : ∀ x ∈ f ⁻¹' t, (mfderiv% f x).IsInvertible) (hmn : m + 1 ≤ n) :
    CMDiff[f ⁻¹' t] m (T% (mpullback I I' f V)) :=
  fun x₀ hx₀ ↦ ContMDiffWithinAt.mpullback_vectorField_preimage (hV _ hx₀) (hf x₀) (hf' _ hx₀) hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version at a point. -/
/-
**VectorField._root_.ContMDiffAt.mpullback_vectorField_preimage** 是 Mathlib 中的一个
引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
Version at a point.
-/
protected lemma _root_.ContMDiffAt.mpullback_vectorField_preimage
    (hV : CMDiffAt m (T% V) (f x₀)) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : m + 1 ≤ n) :
    CMDiffAt m (T% (mpullback I I' f V)) x₀ := by
  simp only [← contMDiffWithinAt_univ] at hV hf hf' ⊢
  simpa using ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`. -/
/-
**VectorField._root_.ContMDiff.mpullback_vectorField** 是 Mathlib 中的一个引理，位于命名空间 `
VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a `C^m` vector field by a `C^n` function with invertible derivat
ive and
with `m + 1 ≤ n` is `C^m`.
-/
protected lemma _root_.ContMDiff.mpullback_vectorField
    (hV : CMDiff m (T% V)) (hf : CMDiff n f)
    (hf' : ∀ x, (mfderiv% f x).IsInvertible) (hmn : m + 1 ≤ n) :
    CMDiff m (T% (mpullback I I' f V)) :=
  fun x ↦ ContMDiffAt.mpullback_vectorField_preimage (hV (f x)) (hf x) (hf' x) hmn
/-
**VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm** 是 Mathlib 中的一个
引理，位于命名空间 `VectorField`。
形式化陈述：contMDiffWithinAt_mpullbackWithin_extChartAt_symm {V : Π (x : M), TangentS
pace I x} (hV : CMDiffAt[s] m (T% V) x) (hs : UniqueMDiff[s]) (hx : x in s) (hmn
 : m + 1 <= n) : CMDiffAt[(extChartAt I x).target inter (extChartAt I x).symm ⁻¹
' s] m (T% (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))) (extCh
artAt I x x)
参数：x : M；hV : CMDiffAt[s] m (T% V) x；hs : UniqueMDiff[s]；hx : x in s；hmn : m + 1
 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq'`：∀ {𝕜 : Type u_1} [
inst : NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {
E : Type u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type 
u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `ContMDiffAdd.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `contMDiffWithinAt_extChartAt_symm_range_self`：contMDiffWithinAt_extChart
At_symm_range_self (x : M) : ContMDiffWithinAt 𝓘(𝕜, E) I n (extChartAt I x).symm
 (range I) (extChartAt I x x)
· 使用引理 `isInvertible_mfderivWithin_extChartAt_symm`：isInvertible_mfderivWithin_e
xtChartAt_symm {y : E} (hy : y in (extChartAt I x).target) : (mfderiv[range I] (
extChartAt I x).symm y).IsInvert…
· 使用定理 `mem_extChartAt_target`：mem_extChartAt_target (x : M) : extChartAt I x x 
in (extChartAt I x).target
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `UniqueMDiffOn.uniqueMDiffOn_target_inter`：UniqueMDiffOn.uniqueMDiffOn_ta
rget_inter (hs : UniqueMDiff[s]) (x : M) : UniqueMDiff[(extChartAt I x).target i
nter (extChartAt I x).symm ⁻¹'…
· 使用引理 `Set.MapsTo.preimage_mem_nhdsWithin`：Set.MapsTo.preimage_mem_nhdsWithin {
f : α -> β} {s : Set α} {t : Set β} {x : α} (hst : MapsTo f s t) : f ⁻¹' t in 𝓝[
s] x
· 使用定理 `Set.MapsTo.mono_left`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t
 : Set β} {f : α → β}, Set.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I
· 使用定理 `extChartAt_to_inv`：extChartAt_to_inv (x : M) : (extChartAt I x).symm ((e
xtChartAt I x) x) = x
-/
lemma contMDiffWithinAt_mpullbackWithin_extChartAt_symm
    {V : Π (x : M), TangentSpace I x} (hV : CMDiffAt[s] m (T% V) x)
    (hs : UniqueMDiff[s]) (hx : x ∈ s) (hmn : m + 1 ≤ n) :
    CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] m
      (T% (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))) (extChartAt I x x) :=
  ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq' hV
    (contMDiffWithinAt_extChartAt_symm_range_self (n := n) x)
    (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x))
    (by simp [hx]) (UniqueMDiffOn.uniqueMDiffOn_target_inter hs x) hmn
    ((mapsTo_preimage _ _).mono_left inter_subset_right).preimage_mem_nhdsWithin
    (Subset.trans inter_subset_left (extChartAt_target_subset_range x)) (extChartAt_to_inv x)
/-
**VectorField.eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm** 是 M
athlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm {V : Π (x : M
), TangentSpace I x} (hV : CMDiffAt[s] m (T% V) x) (hs : UniqueMDiff[s]) (hx : x
 in s) (hmn : m + 1 <= n) (hm : m != ∞) : forallᶠ y in 𝓝[s] x, CMDiffAt[(extChar
tAt I x).target inter (extChartAt I x).symm ⁻¹' s] m (T% (mpullbackWithin 𝓘(𝕜, E
) I (extChartAt I x).symm V (range I))) (extChartAt I x y)
参数：x : M；hV : CMDiffAt[s] m (T% V) x；hs : UniqueMDiff[s]；hx : x in s；hmn : m + 1
 <= n；hm : m != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type 
u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `ContMDiffAdd.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin`：contMDiffWithinAt_if
f_contMDiffWithinAt_nhdsWithin [IsManifold I n M] [IsManifold I' n M'] (hn : n !
= ∞) : ContMDiffWithinAt I I' n f s x ↔ …
· 使用定理 `instContMDiffVectorBundleOfTopWithTopENat`：∀ {𝕜 : Type u_1} {B : Type u_
2} (F : Type u_4) (E : B → Type u_6) [inst : NontriviallyNormedField 𝕜] {EB : Ty
pe u_7}   [inst_1 : NormedAddCo…
· 使用定理 `instContMDiffVectorBundleTopWithTopENatTangentSpaceOfIsManifold`：∀ {𝕜 : 
Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddC
ommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用引理 `VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm`：contMDiff
WithinAt_mpullbackWithin_extChartAt_symm {V : Π (x : M), TangentSpace I x} (hV :
 CMDiffAt[s] m (T% V) x) (hs : UniqueMDiff[s]) (hx …
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin''`：ContinuousWithinAt.preimag
e_mem_nhdsWithin'' {y : β} {s t : Set β} (h : ContinuousWithinAt f (f ⁻¹' s) x) 
(ht : t in 𝓝[s] y) (hxy : y = f x)…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `continuousAt_extChartAt`：continuousAt_extChartAt (x : M) : ContinuousAt 
(extChartAt I x) x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_le_iff`：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝
[t] x ↔ t in 𝓝[s] x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
（共 35 条，此处仅展示前 30 条）
-/
lemma eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm
    {V : Π (x : M), TangentSpace I x} (hV : CMDiffAt[s] m (T% V) x)
    (hs : UniqueMDiff[s]) (hx : x ∈ s) (hmn : m + 1 ≤ n) (hm : m ≠ ∞) :
    ∀ᶠ y in 𝓝[s] x, CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] m
    (T% (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))) (extChartAt I x y) := by
  have T := nhdsWithin_mono _ (subset_insert _ _)
    ((contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin hm).1
      (contMDiffWithinAt_mpullbackWithin_extChartAt_symm hV hs hx hmn))
  have A := (continuousAt_extChartAt (I := I) x).continuousWithinAt.preimage_mem_nhdsWithin'' T rfl
  apply (nhdsWithin_le_iff.2 _) A
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)]
    with y hy h'y
  simp only [mfld_simps] at hy h'y
  simp [hy, h'y]

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] in
/-
**VectorField.eventuallyEq_mpullback_mpullbackWithin_extChartAt** 是 Mathlib 中的一个
引理，位于命名空间 `VectorField`。
形式化陈述：eventuallyEq_mpullback_mpullbackWithin_extChartAt (V : Π (x : M), TangentS
pace I x) : V =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) (mpullbackWithin 𝓘
(𝕜, E) I (extChartAt I x).symm V (range I))
参数：V : Π (x : M), TangentSpace I x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.mpullback_apply`：mpullback_apply : mpullback I I' f V x = (m
fderiv% f x).inverse (V (f x))
· 使用引理 `VectorField.mpullbackWithin_apply`：mpullbackWithin_apply : mpullbackWith
in I I' f V s x = (mfderiv[s] f x).inverse (V (f x))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right`：∀ {R : Typ
e u_1} {M : Type u_2} {M₂ : Type u_3} {M₃ : Type u_4} [inst : TopologicalSpace M
]   [inst_1 : TopologicalSpace M₂] [inst_2 : Topol…
· 使用引理 `isInvertible_mfderiv_extChartAt`：isInvertible_mfderiv_extChartAt {y : M}
 (hy : y in (extChartAt I x).source) : (mfderiv% (extChartAt I x) y).IsInvertibl
e
· 使用引理 `mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'`：mfderivWithin_ex
tChartAt_symm_comp_mfderiv_extChartAt' {y : M} (hy : y in (extChartAt I x).sourc
e) : (mfderiv[range I] (extChartAt I x).symm…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.inverse_id`：∀ {R : Type u_1} {M : Type u_2} [inst : 
TopologicalSpace M] [inst_1 : Semiring R] [inst_2 : AddCommMonoid M]   [inst_3 :
 _root_.Module R M],…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eventuallyEq_mpullback_mpullbackWithin_extChartAt (V : Π (x : M), TangentSpace I x) :
    V =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x)
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)) := by
  apply nhdsWithin_le_nhds
  filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
  have A : (extChartAt I x).symm (extChartAt I x y) = y := (extChartAt I x).left_inv hy
  rw [mpullback_apply, mpullbackWithin_apply,
    ← (isInvertible_mfderiv_extChartAt hy).inverse_comp_apply_of_right,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy, A]
  simp only [ContinuousLinearMap.inverse_id, ContinuousLinearMap.coe_id', id_eq]

end ContMDiff

end Pullback

end VectorField

