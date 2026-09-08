/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.Geometry.Manifold.DerivationBundle

/-!

# Left invariant derivations

In this file we define the concept of left invariant derivations for a Lie group. The concept is
analogous to the more classical concept of left invariant vector fields, and it holds that the
derivation associated to a vector field is left invariant iff the field is.

Moreover we prove that `LeftInvariantDerivation I G` has the structure of a Lie algebra, hence
implementing one of the possible definitions of the Lie algebra attached to a Lie group.

Note that one can also define a Lie algebra on the space of left-invariant vector fields
(see `instLieAlgebraGroupLieAlgebra`). For finite-dimensional `C^∞` real manifolds, the space of
derivations can be canonically identified with the tangent space, and we recover the same Lie
algebra structure (TODO: prove this). In other smoothness classes or on other
fields, this identification is not always true, though, so the derivations point of view does not
work in these settings. The left-invariant vector fields should
therefore be favored to construct a theory of Lie groups in suitable generality.
-/

@[expose] public section


noncomputable section

open scoped LieGroup Manifold Derivation ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (G : Type*)
  [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [ContMDiffMul I ∞ G] (g h : G)

/-- Left-invariant global derivations.

A global derivation is left-invariant if it is equal to its pullback along left multiplication by
an arbitrary element of `G`.
-/
/-
**LeftInvariantDerivation** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     (I : ModelWithCorners 𝕜 E H) →                 (G : Type u_4) →            
       [inst_4 : TopologicalSpace G] →                     [inst_5 : ChartedSpac
e H G] → [inst_6 : Monoid G] → [ContMDiffMul I (↑⊤) G] → Type (max u_1 u_4)
参数：I : ModelWithCorners 𝕜 E H；G : Type u_4；↑⊤；max u_1 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left-invariant global derivations.

A global derivation is left-invariant if it is equal to its pullback along left 
multiplication by
an arbitrary element of `G`.
-/
structure LeftInvariantDerivation extends Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  left_invariant'' :
    ∀ g, 𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt 1 toDerivation) =
      Derivation.evalAt g toDerivation

variable {I G}

namespace LeftInvariantDerivation

/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (LeftInvariantDerivation I G) (Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  ⟨toDerivation⟩

attribute [coe] toDerivation
/-
**LeftInvariantDerivation.toDerivation_injective** 是 Mathlib 中的一个定理，位于命名空间 `Left
InvariantDerivation`。
形式化陈述：toDerivation_injective : Function.Injective (toDerivation : LeftInvariantD
erivation I G -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTop`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `smoothLeftMul_one`：smoothLeftMul_one : (𝑳 I g') 1 = g'
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTopContMDiffMapModelWithCor
nersSelf`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [in
st_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toDerivation_injective :
    Function.Injective (toDerivation : LeftInvariantDerivation I G → _) :=
  fun X Y h => by cases X; cases Y; congr
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (LeftInvariantDerivation I G) C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  coe f := f.toDerivation
  coe_injective _ _ h := toDerivation_injective <| DFunLike.ext' h
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearMapClass (LeftInvariantDerivation I G) 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  map_add f := map_add f.1
  map_smulₛₗ f := map_smul f.1.1

variable {r : 𝕜} {X Y : LeftInvariantDerivation I G} {f f' : C^∞⟮I, G; 𝕜⟯}
/-
**LeftInvariantDerivation.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantD
erivation`。
形式化陈述：toFun_eq_coe : X.toFun = ⇑X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
-/
theorem toFun_eq_coe : X.toFun = ⇑X :=
  rfl
/-
**LeftInvariantDerivation.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariant
Derivation`。
形式化陈述：coe_injective : @Function.Injective (LeftInvariantDerivation I G) (_ -> C^
∞⟮I, G; 𝕜⟯) DFunLike.coe
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective :
    @Function.Injective (LeftInvariantDerivation I G) (_ → C^∞⟮I, G; 𝕜⟯) DFunLike.coe :=
  DFunLike.coe_injective

@[ext]
/-
**LeftInvariantDerivation.ext** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDerivation
`。
形式化陈述：ext (h : forall f, X f = Y f) : X = Y
参数：h : forall f, X f = Y f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ f, X f = Y f) : X = Y := DFunLike.ext _ _ h

variable (X Y f)
/-
**LeftInvariantDerivation.coe_derivation** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvarian
tDerivation`。
形式化陈述：coe_derivation : ⇑(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = (X : C^∞⟮
I, G; 𝕜⟯ -> C^∞⟮I, G; 𝕜⟯)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
-/
theorem coe_derivation :
    ⇑(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = (X : C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯) :=
  rfl

/-- Premature version of the lemma. Prefer using `left_invariant` instead. -/
/-
**LeftInvariantDerivation.left_invariant'** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvaria
ntDerivation`。
形式化陈述：left_invariant' : 𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt (1 : G) ↑X
) = Derivation.evalAt g ↑X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftInvariantDerivation.left_invariant''`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
Premature version of the lemma. Prefer using `left_invariant` instead.
-/
theorem left_invariant' :
    𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt (1 : G) ↑X) = Derivation.evalAt g ↑X :=
  left_invariant'' X g
/-
**LeftInvariantDerivation.map_add** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriva
tion`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {G : Type u_4}   [inst_4 : Topol
ogicalSpace G] [inst_5 : ChartedSpace H G] [inst_6 : Monoid G] [inst_7 : ContMDi
ffMul I (↑⊤) G]   (X : LeftInvariantDerivation I G) (f : ContMDiffMap I (modelWi
thCornersSelf 𝕜 𝕜) G 𝕜 ↑⊤)   {f' : ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) G 𝕜
 ↑⊤}, X (f + f') = X f + X f'
参数：↑⊤；X : LeftInvariantDerivation I G；f : ContMDiffMap I (modelWithCornersSelf 𝕜
 𝕜) G 𝕜 ↑⊤；modelWithCornersSelf 𝕜 𝕜；f + f'。
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
· 使用定理 `LeftInvariantDerivation.instLinearMapClassContMDiffMapModelWithCornersSe
lfSomeENatTop`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2
} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_add : X (f + f') = X f + X f' := by simp
/-
**LeftInvariantDerivation.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriv
ation`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {G : Type u_4}   [inst_4 : Topol
ogicalSpace G] [inst_5 : ChartedSpace H G] [inst_6 : Monoid G] [inst_7 : ContMDi
ffMul I (↑⊤) G]   (X : LeftInvariantDerivation I G), X 0 = 0
参数：↑⊤；X : LeftInvariantDerivation I G。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `LeftInvariantDerivation.instLinearMapClassContMDiffMapModelWithCornersSe
lfSomeENatTop`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2
} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_zero : X 0 = 0 := by simp
/-
**LeftInvariantDerivation.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriva
tion`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {G : Type u_4}   [inst_4 : Topol
ogicalSpace G] [inst_5 : ChartedSpace H G] [inst_6 : Monoid G] [inst_7 : ContMDi
ffMul I (↑⊤) G]   (X : LeftInvariantDerivation I G) (f : ContMDiffMap I (modelWi
thCornersSelf 𝕜 𝕜) G 𝕜 ↑⊤), X (-f) = -X f
参数：↑⊤；X : LeftInvariantDerivation I G；f : ContMDiffMap I (modelWithCornersSelf 𝕜
 𝕜) G 𝕜 ↑⊤；-f。
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
· 使用定理 `LeftInvariantDerivation.instLinearMapClassContMDiffMapModelWithCornersSe
lfSomeENatTop`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2
} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_neg : X (-f) = -X f := by simp
/-
**LeftInvariantDerivation.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriva
tion`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {G : Type u_4}   [inst_4 : Topol
ogicalSpace G] [inst_5 : ChartedSpace H G] [inst_6 : Monoid G] [inst_7 : ContMDi
ffMul I (↑⊤) G]   (X : LeftInvariantDerivation I G) (f : ContMDiffMap I (modelWi
thCornersSelf 𝕜 𝕜) G 𝕜 ↑⊤)   {f' : ContMDiffMap I (modelWithCornersSelf 𝕜 𝕜) G 𝕜
 ↑⊤}, X (f - f') = X f - X f'
参数：↑⊤；X : LeftInvariantDerivation I G；f : ContMDiffMap I (modelWithCornersSelf 𝕜
 𝕜) G 𝕜 ↑⊤；modelWithCornersSelf 𝕜 𝕜；f - f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LeftInvariantDerivation.instLinearMapClassContMDiffMapModelWithCornersSe
lfSomeENatTop`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2
} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_sub : X (f - f') = X f - X f' := by simp

set_option backward.isDefEq.respectTransparency false in
/-
**LeftInvariantDerivation.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriv
ation`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {G : Type u_4}   [inst_4 : Topol
ogicalSpace G] [inst_5 : ChartedSpace H G] [inst_6 : Monoid G] [inst_7 : ContMDi
ffMul I (↑⊤) G] {r : 𝕜}   (X : LeftInvariantDerivation I G) (f : ContMDiffMap I 
(modelWithCornersSelf 𝕜 𝕜) G 𝕜 ↑⊤), X (r • f) = r • X f
参数：↑⊤；X : LeftInvariantDerivation I G；f : ContMDiffMap I (modelWithCornersSelf 𝕜
 𝕜) G 𝕜 ↑⊤；r • f。
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
· 使用定理 `LeftInvariantDerivation.instLinearMapClassContMDiffMapModelWithCornersSe
lfSomeENatTop`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2
} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_smul : X (r • f) = r • X f := by simp

@[simp]
/-
**LeftInvariantDerivation.leibniz** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriva
tion`。
形式化陈述：leibniz : X (f * f') = f • X f' + f' • X f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.leibniz'`：∀ {R : Type u_1} {A : Type u_2} {M : Type u_3} [ins
t : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMonoid M] [inst
_3 : Alge…
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
-/
theorem leibniz : X (f * f') = f • X f' + f' • X f :=
  X.leibniz' _ _
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (LeftInvariantDerivation I G) :=
  ⟨⟨0, fun g => by simp only [map_zero]⟩⟩
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LeftInvariantDerivation I G) :=
  ⟨0⟩
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (LeftInvariantDerivation I G) where
  add X Y :=
    ⟨X + Y, fun g => by
      simp only [map_add, left_invariant']⟩
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (LeftInvariantDerivation I G) where
  neg X := ⟨-X, fun g => by simp [left_invariant']⟩
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (LeftInvariantDerivation I G) where
  sub X Y := ⟨X - Y, fun g => by simp [left_invariant']⟩

@[simp]
/-
**LeftInvariantDerivation.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriva
tion`。
形式化陈述：coe_add : ⇑(X + Y) = X + Y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add : ⇑(X + Y) = X + Y :=
  rfl

@[simp]
/-
**LeftInvariantDerivation.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriv
ation`。
形式化陈述：coe_zero : ⇑(0 : LeftInvariantDerivation I G) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : LeftInvariantDerivation I G) = 0 :=
  rfl

@[simp]
/-
**LeftInvariantDerivation.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriva
tion`。
形式化陈述：coe_neg : ⇑(-X) = -X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg : ⇑(-X) = -X :=
  rfl

@[simp]
/-
**LeftInvariantDerivation.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriva
tion`。
形式化陈述：coe_sub : ⇑(X - Y) = X - Y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub : ⇑(X - Y) = X - Y :=
  rfl

@[simp, norm_cast]
/-
**LeftInvariantDerivation.lift_add** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriv
ation`。
形式化陈述：lift_add : (↑(X + Y) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = X + Y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
-/
theorem lift_add : (↑(X + Y) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = X + Y :=
  rfl

@[simp, norm_cast]
/-
**LeftInvariantDerivation.lift_zero** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeri
vation`。
形式化陈述：lift_zero : (↑(0 : LeftInvariantDerivation I G) : Derivation 𝕜 C^∞⟮I, G; 𝕜
⟯ C^∞⟮I, G; 𝕜⟯) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
-/
theorem lift_zero :
    (↑(0 : LeftInvariantDerivation I G) : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) = 0 :=
  rfl
/-
**LeftInvariantDerivation.hasNatScalar** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantD
erivation`。
形式化陈述：hasNatScalar : SMul Nat (LeftInvariantDerivation I G) where smul r X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNatScalar : SMul ℕ (LeftInvariantDerivation I G) where
  smul r X := ⟨r • X.1, fun g => by simp_rw [LinearMap.map_smul_of_tower _ r, left_invariant']⟩
/-
**LeftInvariantDerivation.hasIntScalar** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantD
erivation`。
形式化陈述：hasIntScalar : SMul Int (LeftInvariantDerivation I G) where smul r X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasIntScalar : SMul ℤ (LeftInvariantDerivation I G) where
  smul r X := ⟨r • X.1, fun g => by simp_rw [LinearMap.map_smul_of_tower _ r, left_invariant']⟩
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (LeftInvariantDerivation I G) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul 𝕜 (LeftInvariantDerivation I G) where
  smul r X := ⟨r • X.1, fun g => by
    simp only [LinearMap.map_smul_of_tower, map_smul]; rw [left_invariant']⟩

variable (r)

@[simp]
/-
**LeftInvariantDerivation.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeriv
ation`。
形式化陈述：coe_smul : ⇑(r • X) = r • ⇑X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul : ⇑(r • X) = r • ⇑X :=
  rfl

@[simp]
/-
**LeftInvariantDerivation.lift_smul** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDeri
vation`。
形式化陈述：lift_smul (k : 𝕜) : (k • X).1 = k • X.1
参数：k : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
-/
theorem lift_smul (k : 𝕜) : (k • X).1 = k • X.1 :=
  rfl

variable (I G)

/-- The coercion to function is a monoid homomorphism. -/
@[simps]
/-
**LeftInvariantDerivation.coeFnAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LeftInvar
iantDerivation`。
形式化陈述：coeFnAddMonoidHom : LeftInvariantDerivation I G ->+ C^∞⟮I, G; 𝕜⟯ -> C^∞⟮I,
 G; 𝕜⟯
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LeftInvariantDerivation.coe_zero`：coe_zero : ⇑(0 : LeftInvariantDerivati
on I G) = 0
· 使用定理 `LeftInvariantDerivation.coe_add`：coe_add : ⇑(X + Y) = X + Y

--- 原说明 ---
The coercion to function is a monoid homomorphism.
-/
def coeFnAddMonoidHom : LeftInvariantDerivation I G →+ C^∞⟮I, G; 𝕜⟯ → C^∞⟮I, G; 𝕜⟯ :=
  ⟨⟨DFunLike.coe, coe_zero⟩, coe_add⟩

variable {I G}
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module 𝕜 (LeftInvariantDerivation I G) :=
  coe_injective.module _ (coeFnAddMonoidHom I G) coe_smul

/-- Evaluation at a point for left invariant derivations. Same thing as for generic global
derivations (`Derivation.evalAt`). -/
/-
**LeftInvariantDerivation.evalAt** 是 Mathlib 中的一个定义，位于命名空间 `LeftInvariantDerivat
ion`。
形式化陈述：evalAt : LeftInvariantDerivation I G ->ₗ[𝕜] PointDerivation I g where toFu
n X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation at a point for left invariant derivations. Same thing as for generic 
global
derivations (`Derivation.evalAt`).
-/
def evalAt : LeftInvariantDerivation I G →ₗ[𝕜] PointDerivation I g where
  toFun X := Derivation.evalAt g X.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-
**LeftInvariantDerivation.evalAt_apply** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantD
erivation`。
形式化陈述：evalAt_apply : evalAt g X f = (X f) g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTop`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {H : Type u_…
-/
theorem evalAt_apply : evalAt g X f = (X f) g :=
  rfl

@[simp]
/-
**LeftInvariantDerivation.evalAt_coe** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDer
ivation`。
形式化陈述：evalAt_coe : Derivation.evalAt g ↑X = evalAt g X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTopContMDiffMapModelWithCor
nersSelf`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [in
st_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTop`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {H : Type u_…
-/
theorem evalAt_coe : Derivation.evalAt g ↑X = evalAt g X :=
  rfl
/-
**LeftInvariantDerivation.left_invariant** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvarian
tDerivation`。
形式化陈述：left_invariant : 𝒅ₕ (smoothLeftMul_one I g) (evalAt (1 : G) X) = evalAt g 
X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftInvariantDerivation.left_invariant''`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] {H : Type u_…
-/
theorem left_invariant : 𝒅ₕ (smoothLeftMul_one I g) (evalAt (1 : G) X) = evalAt g X :=
  X.left_invariant'' g

set_option backward.isDefEq.respectTransparency false in
/-
**LeftInvariantDerivation.evalAt_mul** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDer
ivation`。
形式化陈述：evalAt_mul : evalAt (g * h) X = 𝒅ₕ (L_apply I g h) (evalAt h X)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTop`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `L_apply`：L_apply : (𝑳 I g) h = g * h
· 使用定理 `smoothLeftMul_one`：smoothLeftMul_one : (𝑳 I g') 1 = g'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LeftInvariantDerivation.left_invariant`：left_invariant : 𝒅ₕ (smoothLeftM
ul_one I g) (evalAt (1 : G) X) = evalAt g X
· 使用定理 `hfdifferential_apply`：hfdifferential_apply {f : C^∞⟮I, M; I', M'⟯} {x : 
M} {y : M'} (h : f x = y) (v : PointDerivation I x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅ₕ h 
v g = 𝒅 f …
· 使用定理 `L_mul`：L_mul {G : Type*} [Semigroup G] [TopologicalSpace G] [ChartedSpac
e H G] [ContMDiffMul I ∞ G] (g h : G) : 𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h)
· 使用定理 `fdifferential_comp`：fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : 
C^∞⟮I, M; I', M'⟯) (x : M) : 𝒅 (g.comp f) x = (𝒅 g (f x)).comp (𝒅 f x)
· 使用定理 `fdifferential_apply`：fdifferential_apply (f : C^∞⟮I, M; I', M'⟯) {x : M}
 (v : PointDerivation I x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅 f x v g = v (g.comp f)
-/
theorem evalAt_mul : evalAt (g * h) X = 𝒅ₕ (L_apply I g h) (evalAt h X) := by
  ext f
  rw [← left_invariant, hfdifferential_apply, hfdifferential_apply, L_mul, fdifferential_comp,
    fdifferential_apply]
  simp only [ContMDiffMap.comp_apply, LinearMap.comp_apply]
  rw [fdifferential_apply, ← hfdifferential_apply (smoothLeftMul_one I h), left_invariant]
/-
**LeftInvariantDerivation.comp_L** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvariantDerivat
ion`。
形式化陈述：comp_L : (X f).comp (𝑳 I g) = X (f.comp (𝑳 I g))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffMap.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContMDiffMap.comp_apply`：comp_apply (f : C^n⟮I', M'; I'', M''⟯) (g : C^n
⟮I, M; I', M'⟯) (x : M) : f.comp g x = f (g x)
· 使用定理 `L_apply`：L_apply : (𝑳 I g) h = g * h
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTop`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LeftInvariantDerivation.evalAt_apply`：evalAt_apply : evalAt g X f = (X f
) g
· 使用定理 `LeftInvariantDerivation.evalAt_mul`：evalAt_mul : evalAt (g * h) X = 𝒅ₕ (
L_apply I g h) (evalAt h X)
· 使用定理 `hfdifferential_apply`：hfdifferential_apply {f : C^∞⟮I, M; I', M'⟯} {x : 
M} {y : M'} (h : f x = y) (v : PointDerivation I x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅ₕ h 
v g = 𝒅 f …
· 使用定理 `fdifferential_apply`：fdifferential_apply (f : C^∞⟮I, M; I', M'⟯) {x : M}
 (v : PointDerivation I x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅 f x v g = v (g.comp f)
-/
theorem comp_L : (X f).comp (𝑳 I g) = X (f.comp (𝑳 I g)) := by
  ext h
  rw [ContMDiffMap.comp_apply, L_apply, ← evalAt_apply, evalAt_mul, hfdifferential_apply,
    fdifferential_apply, evalAt_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bracket (LeftInvariantDerivation I G) (LeftInvariantDerivation I G) where
  bracket X Y :=
    ⟨⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆, fun g => by
      ext f
      have hX := Derivation.congr_fun (left_invariant' g X) (Y f)
      have hY := Derivation.congr_fun (left_invariant' g Y) (X f)
      rw [hfdifferential_apply, fdifferential_apply, Derivation.evalAt_apply] at hX hY ⊢
      rw [comp_L] at hX hY
      rw [Derivation.commutator_apply, ContMDiffMap.coe_sub, Pi.sub_apply, coe_derivation]
      rw [coe_derivation] at hX hY ⊢
      rw [hX, hY]
      rfl⟩

@[simp]
/-
**LeftInvariantDerivation.commutator_coe_derivation** 是 Mathlib 中的一个定理，位于命名空间 `L
eftInvariantDerivation`。
形式化陈述：commutator_coe_derivation : ⇑⁅X, Y⁆ = (⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞
⟮I, G; 𝕜⟯), Y⁆ : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commutator_coe_derivation :
    ⇑⁅X, Y⁆ =
      (⁅(X : Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯), Y⁆ :
        Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯) :=
  rfl
/-
**LeftInvariantDerivation.commutator_apply** 是 Mathlib 中的一个定理，位于命名空间 `LeftInvari
antDerivation`。
形式化陈述：commutator_apply : ⁅X, Y⁆ f = X (Y f) - Y (X f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commutator_apply : ⁅X, Y⁆ f = X (Y f) - Y (X f) :=
  rfl
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRing (LeftInvariantDerivation I G) where
  add_lie X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, Pi.add_apply, map_add]
    ring
  lie_add X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, Pi.add_apply, map_add]
    ring
  lie_self X := by ext1; simp only [commutator_apply, sub_self]; rfl
  leibniz_lie X Y Z := by
    ext1
    simp only [commutator_apply, coe_add, map_sub, Pi.add_apply]
    ring

set_option backward.isDefEq.respectTransparency false in
/-
**LeftInvariantDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LeftInvariantDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieAlgebra 𝕜 (LeftInvariantDerivation I G) where
  lie_smul r Y Z := by
    ext1
    simp only [commutator_apply, map_smul, smul_sub, coe_smul, Pi.smul_apply]

end LeftInvariantDerivation

