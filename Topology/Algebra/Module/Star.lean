/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Star

/-!
# The star operation, bundled as a continuous star-linear equiv
-/

@[expose] public section



@[inherit_doc]
notation:25 M " →L⋆[" R "] " M₂ => ContinuousLinearMap (starRingEnd R) M M₂

@[inherit_doc]
notation:50 M " ≃L⋆[" R "] " M₂ => ContinuousLinearEquiv (starRingEnd R) M M₂

section starL

variable (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A]

set_option backward.defeqAttrib.useBackward true in
/-- If `A` is a topological module over a commutative `R` with compatible actions,
then `star` is a continuous semilinear equivalence. -/
@[simps! apply]
/-
**starL** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starL : A ≃L⋆[R] A where toLinearEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)

--- 原说明 ---
If `A` is a topological module over a commutative `R` with compatible actions,
then `star` is a continuous semilinear equivalence.
-/
def starL : A ≃L⋆[R] A where
  toLinearEquiv := starLinearEquiv R

@[simp]
/-
**toLinearEquiv_starL** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toLinearEquiv_starL : (starL R : A ≃L⋆[R] A).toLinearEquiv = starLinearEqu
iv R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
-/
theorem toLinearEquiv_starL : (starL R : A ≃L⋆[R] A).toLinearEquiv = starLinearEquiv R :=
  rfl

@[simp]
/-
**symm_starL** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symm_starL : (starL R : A ≃L⋆[R] A).symm = starL R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
-/
theorem symm_starL : (starL R : A ≃L⋆[R] A).symm = starL R :=
  rfl

@[deprecated "Use `symm_starL` and `starL_apply` instead" (since := "2026-06-03")]
/-
**starL_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：starL_symm_apply (x : A) : (starL R).symm x = starAddEquiv.symm x
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `starL_apply`：∀ (R : Type u_1) {A : Type u_2} [inst : CommSemiring R] [in
st_1 : StarRing R] [inst_2 : AddCommMonoid A]   [inst_3 : StarAddMonoid A] [inst
_…
· 使用定理 `starAddEquiv_apply`：∀ {R : Type u} [inst : AddMonoid R] [inst_1 : StarAd
dMonoid R] (a : R), starAddEquiv a = star a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem starL_symm_apply (x : A) : (starL R).symm x = starAddEquiv.symm x := by
  simp

variable [TrivialStar R]

-- TODO: this could be replaced with something like `(starL R).restrict_scalarsₛₗ h` if we
-- implemented the idea in
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Star-semilinear.20maps.20are.20semilinear.20when.20star.20is.20trivial/near/359557835
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- If `A` is a topological module over a commutative `R` with trivial star and compatible actions,
then `star` is a continuous linear equivalence. -/
@[simps! apply]
/-
**starL'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：starL' : A ≃L[R] A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
If `A` is a topological module over a commutative `R` with trivial star and comp
atible actions,
then `star` is a continuous linear equivalence.
-/
def starL' : A ≃L[R] A :=
  (starL R : A ≃L⋆[R] A).trans
    ({ AddEquiv.refl A with
        map_smul' := fun r a => by simp
        continuous_toFun := continuous_id
        continuous_invFun := continuous_id } :
      A ≃L⋆[R] A)

@[simp]
/-
**symm_starL'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：symm_starL' : (starL' R : A ≃L[R] A).symm = starL' R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_starL' : (starL' R : A ≃L[R] A).symm = starL' R :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[deprecated "Use `symm_starL'` and `starL'_apply` instead" (since := "2026-06-03")]
/-
**starL'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) {A : Type u_2} [inst : CommSemiring R] [inst_1 : StarRing
 R] [inst_2 : AddCommMonoid A]   [inst_3 : StarAddMonoid A] [inst_4 : _root_.Mod
ule R A] [inst_5 : StarModule R A] [inst_6 : TopologicalSpace A]   [inst_7 : Con
tinuousStar A] [inst_8 : TrivialStar R] (x : A), (starL' R).symm x = starAddEqui
v.symm x
参数：R : Type u_1；x : A；starL' R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `starL'_apply`：∀ (R : Type u_1) {A : Type u_2} [inst : CommSemiring R] [i
nst_1 : StarRing R] [inst_2 : AddCommMonoid A]   [inst_3 : StarAddMonoid A] [ins
t_…
· 使用定理 `starAddEquiv_apply`：∀ {R : Type u} [inst : AddMonoid R] [inst_1 : StarAd
dMonoid R] (a : R), starAddEquiv a = star a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem starL'_symm_apply (x : A) : (starL' R).symm x = starAddEquiv.symm x := by
  simp

end starL

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A] [Invertible (2 : R)] [TopologicalSpace A]

@[fun_prop]
/-
**continuous_selfAdjointPart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_selfAdjointPart [ContinuousAdd A] [ContinuousStar A] [Continuou
sConstSMul R A] : Continuous (selfAdjointPart R (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
theorem continuous_selfAdjointPart [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (selfAdjointPart R (A := A)) :=
  ((continuous_const_smul _).comp <| continuous_id.add continuous_star).subtype_mk _

@[fun_prop]
/-
**continuous_skewAdjointPart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_skewAdjointPart [ContinuousSub A] [ContinuousStar A] [Continuou
sConstSMul R A] : Continuous (skewAdjointPart R (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
theorem continuous_skewAdjointPart [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (skewAdjointPart R (A := A)) :=
  ((continuous_const_smul _).comp <| continuous_id.sub continuous_star).subtype_mk _

@[fun_prop]
/-
**continuous_decomposeProdAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_decomposeProdAdjoint [IsTopologicalAddGroup A] [ContinuousStar 
A] [ContinuousConstSMul R A] : Continuous (StarModule.decomposeProdAdjoint R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_selfAdjointPart`：continuous_selfAdjointPart [ContinuousAdd A]
 [ContinuousStar A] [ContinuousConstSMul R A] : Continuous (selfAdjointPart R (A
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `continuous_skewAdjointPart`：continuous_skewAdjointPart [ContinuousSub A]
 [ContinuousStar A] [ContinuousConstSMul R A] : Continuous (skewAdjointPart R (A
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
-/
theorem continuous_decomposeProdAdjoint [IsTopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : Continuous (StarModule.decomposeProdAdjoint R A) :=
  (continuous_selfAdjointPart R A).prodMk (continuous_skewAdjointPart R A)

@[fun_prop]
/-
**continuous_decomposeProdAdjoint_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_decomposeProdAdjoint_symm [ContinuousAdd A] : Continuous (StarM
odule.decomposeProdAdjoint R A).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem continuous_decomposeProdAdjoint_symm [ContinuousAdd A] :
    Continuous (StarModule.decomposeProdAdjoint R A).symm :=
  (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

/-- The self-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps! -isSimp]
/-
**selfAdjointPartL** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：selfAdjointPartL [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul
 R A] : A ->L[R] selfAdjoint A where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The self-adjoint part of an element of a star module, as a continuous linear map
.
-/
def selfAdjointPartL [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] selfAdjoint A where
  toLinearMap := selfAdjointPart R

/-- The skew-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps!]
/-
**skewAdjointPartL** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjointPartL [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul
 R A] : A ->L[R] skewAdjoint A where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The skew-adjoint part of an element of a star module, as a continuous linear map
.
-/
def skewAdjointPartL [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A →L[R] skewAdjoint A where
  toLinearMap := skewAdjointPart R

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a continuous linear equivalence. -/
@[simps!]
/-
**StarModule.decomposeProdAdjointL** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：StarModule.decomposeProdAdjointL [IsTopologicalAddGroup A] [ContinuousStar
 A] [ContinuousConstSMul R A] : A ≃L[R] selfAdjoint A × skewAdjoint A where toLi
nearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The decomposition of elements of a star module into their self- and skew-adjoint
 parts,
as a continuous linear equivalence.
-/
def StarModule.decomposeProdAdjointL [IsTopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : A ≃L[R] selfAdjoint A × skewAdjoint A where
  toLinearEquiv := StarModule.decomposeProdAdjoint R A
