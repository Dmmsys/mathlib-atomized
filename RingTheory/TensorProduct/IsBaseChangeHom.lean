/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Determinant

/-! # Base change properties for modules of linear maps

* `IsBaseChange.linearMapRight`:
  If `M` is finite free and `P` is a base change of `N` to `S`,
  then `M →ₗ[R] P` is a base change of `M →ₗ[R] N` to `S`.

* `IsBaseChange.linearMapLeftRight`:
  If `M` is finite free and `P` is a base change of `M` to `S`,
  if `Q` is a base change of `N` to `S`,
  then `P →ₗ[S] Q` is a base change of `M →ₗ[R] N` to `S`.

* `IsBaseChange.end`:
  If `M` is finite free and `P` is a base change of `M` to `S`,
  then `P →ₗ[S] P` is a base change of `M →ₗ[R] M` to `S`.

-/

@[expose] public section

namespace IsBaseChange

open LinearMap TensorProduct Module

variable {R : Type*} [CommSemiring R]
    (S : Type*) [CommSemiring S] [Algebra R S]
    (M : Type*) [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    {P : Type*} [AddCommMonoid P] [Module R P]

section LinearMapRight

variable [Module S P] [IsScalarTower R S P]

/-- The base change homomorphism underlying `IsBaseChange.linearMapRight` -/
/-
**IsBaseChange.linearMapRightBaseChangeHom** 是 Mathlib 中的一个定义，位于命名空间 `IsBaseChan
ge`。
形式化陈述：linearMapRightBaseChangeHom (ε : N ->ₗ[R] P) : (S otimes[R] (M ->ₗ[R] N)) 
->ₗ[S] (M ->ₗ[R] P) where toAddHom
参数：ε : N ->ₗ[R] P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base change homomorphism underlying `IsBaseChange.linearMapRight`
-/
def linearMapRightBaseChangeHom (ε : N →ₗ[R] P) :
    (S ⊗[R] (M →ₗ[R] N)) →ₗ[S] (M →ₗ[R] P) where
  toAddHom := (TensorProduct.lift {
    toFun s := s • (LinearMap.compRight R ε (M := M))
    map_add' x y := by ext; simp [add_smul]
    map_smul' r s := by simp }).toAddHom
  map_smul' s x := by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [smul_add, hx, hy]
    | tmul t f => simp [TensorProduct.smul_tmul', mul_smul]

variable [Free R M] [Module.Finite R M]

variable {S}

/-- The base change isomorphism underlying `IsBaseChange.linearMapRight` -/
/-
**IsBaseChange.linearMapRightBaseChangeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsBaseCh
ange`。
形式化陈述：linearMapRightBaseChangeEquiv {ε : N ->ₗ[R] P} (ibc : IsBaseChange S ε) : 
S otimes[R] (M ->ₗ[R] N) ≃ₗ[S] (M ->ₗ[R] P)
参数：ibc : IsBaseChange S ε。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base change isomorphism underlying `IsBaseChange.linearMapRight`
-/
noncomputable def linearMapRightBaseChangeEquiv
    {ε : N →ₗ[R] P} (ibc : IsBaseChange S ε) :
    S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] (M →ₗ[R] P) := by
  apply LinearEquiv.ofBijective (linearMapRightBaseChangeHom S M ε)
  let b := Free.chooseBasis R M
  set ι := Free.ChooseBasisIndex R M
  have := Free.ChooseBasisIndex.fintype R M
  let e := (b.repr.congrLeft N R).trans (Finsupp.llift N R R ι).symm
  let f := (b.repr.congrLeft P S).trans (Finsupp.llift P R S ι).symm
  let h := linearMapRightBaseChangeHom S M ε
  let e' : S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] S ⊗[R] (ι → N) :=
    LinearEquiv.baseChange R S (M →ₗ[R] N) (ι → N) e
  let h' := (f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε)).comp e'.symm.toLinearMap
  suffices Function.Bijective h' by simpa [h'] using this
  suffices h' = (finitePow ι ibc).equiv by
    simp only [this]
    apply LinearEquiv.bijective
  suffices f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε) =
      (finitePow ι ibc).equiv.toLinearMap.comp e'.toLinearMap by
    simp [h', this, ← LinearEquiv.trans_assoc e'.symm e']
  ext φ i
  simp
  simp [f, e', linearMapRightBaseChangeHom, LinearEquiv.baseChange, equiv_tmul,
    LinearEquiv.congrLeft, e]

/-- If `M` has a finite basis and `P` is a base change of `N` to `S`,
then `M →ₗ[R] P` is a base change of `M →ₗ[R] N` to `S`. -/
/-
**IsBaseChange.linearMapRight** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：linearMapRight {ε : N ->ₗ[R] P} (ibc : IsBaseChange S ε) : IsBaseChange S 
(LinearMap.compRight (M
参数：ibc : IsBaseChange S ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` has a finite basis and `P` is a base change of `N` to `S`,
then `M →ₗ[R] P` is a base change of `M →ₗ[R] N` to `S`.
-/
theorem linearMapRight {ε : N →ₗ[R] P} (ibc : IsBaseChange S ε) :
    IsBaseChange S (LinearMap.compRight (M := M) R ε) := by
  apply of_equiv (linearMapRightBaseChangeEquiv M ibc)
  intro f
  simp [linearMapRightBaseChangeEquiv, linearMapRightBaseChangeHom]

end LinearMapRight

section LinearMapLeftRight

variable {S M}
  {Q : Type*} [AddCommMonoid Q] [Module R Q]
  [Module S P] [IsScalarTower R S P]
  [Module S Q] [IsScalarTower R S Q]

/-- The base change map for linear maps with source a free finite module. -/
/-
**IsBaseChange.linearMapLeftRightHom** 是 Mathlib 中的一个定义，位于命名空间 `IsBaseChange`。
形式化陈述：linearMapLeftRightHom {α : M ->ₗ[R] P} (j : IsBaseChange S α) (β : N ->ₗ[R
] Q) : (M ->ₗ[R] N) ->ₗ[R] (P ->ₗ[S] Q)
参数：j : IsBaseChange S α；β : N ->ₗ[R] Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base change map for linear maps with source a free finite module.
-/
noncomputable def linearMapLeftRightHom {α : M →ₗ[R] P} (j : IsBaseChange S α)
    (β : N →ₗ[R] Q) :
    (M →ₗ[R] N) →ₗ[R] (P →ₗ[S] Q) :=
  ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S ⊗[R] M) Q).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R β (M := M))
/-
**IsBaseChange.linearMapLeftRightHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChan
ge`。
形式化陈述：linearMapLeftRightHom_apply {α : M ->ₗ[R] P} (j : IsBaseChange S α) (β : N
 ->ₗ[R] Q) (f : M ->ₗ[R] N) (p : P) : linearMapLeftRightHom j β f p = ((liftBase
ChangeEquiv S) (β ∘ₗ f)) (j.equiv.symm p)
参数：j : IsBaseChange S α；β : N ->ₗ[R] Q；f : M ->ₗ[R] N；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
theorem linearMapLeftRightHom_apply
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (β : N →ₗ[R] Q) (f : M →ₗ[R] N) (p : P) :
    linearMapLeftRightHom j β f p = ((liftBaseChangeEquiv S) (β ∘ₗ f)) (j.equiv.symm p) := by
  rfl
/-
**IsBaseChange.linearMapLeftRightHom_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsBas
eChange`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Type u_2} [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S] {M : Type u_3}   [inst_3 : AddCommMonoid M] [inst
_4 : _root_.Module R M] {N : Type u_4} [inst_5 : AddCommMonoid N]   [inst_6 : _r
oot_.Module R N] {P : Type u_5} [inst_7 : AddCommMonoid P] [inst_8 : _root_.Modu
le R P] {Q : Type u_6}   [inst_9 : AddCommMonoid Q] [inst_10 : _root_.Module R Q
] [inst_11 : _root_.Module S P] [inst_12 : IsScalarTower R S P]   [inst_13 : _ro
ot_.Module S Q] [inst_14 : IsScalarTower R S Q] {α : M →ₗ[R] P} (j : IsBaseChang
e S α) (β : N →ₗ[R] Q)   (f : M →ₗ[R] N) (m : M), ((j.linearMapLeftRightHom β) f
) (α m) = β (f m)
参数：j : IsBaseChange S α；β : N →ₗ[R] Q；f : M →ₗ[R] N；m : M；(j.linearMapLeftRightH
om β) f；α m；f m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsBaseChange.linearMapLeftRightHom_apply`：linearMapLeftRightHom_apply {α
 : M ->ₗ[R] P} (j : IsBaseChange S α) (β : N ->ₗ[R] Q) (f : M ->ₗ[R] N) (p : P) 
: linearMapLeftRightHom j β f …
· 使用定理 `IsBaseChange.equiv_symm_apply`：IsBaseChange.equiv_symm_apply (m : M) : h
.equiv.symm (f m) = 1 otimesₜ m
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem linearMapLeftRightHom_comp_apply
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (β : N →ₗ[R] Q) (f : M →ₗ[R] N) (m : M) :
    linearMapLeftRightHom j β f (α m) = β (f m) := by
  simp [linearMapLeftRightHom_apply, IsBaseChange.equiv_symm_apply]
/-
**IsBaseChange.linearMapLeftRightHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChang
e`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Type u_2} [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S] {M : Type u_3}   [inst_3 : AddCommMonoid M] [inst
_4 : _root_.Module R M] {N : Type u_4} [inst_5 : AddCommMonoid N]   [inst_6 : _r
oot_.Module R N] {P : Type u_5} [inst_7 : AddCommMonoid P] [inst_8 : _root_.Modu
le R P] {Q : Type u_6}   [inst_9 : AddCommMonoid Q] [inst_10 : _root_.Module R Q
] [inst_11 : _root_.Module S P] [inst_12 : IsScalarTower R S P]   [inst_13 : _ro
ot_.Module S Q] [inst_14 : IsScalarTower R S Q] {α : M →ₗ[R] P} (j : IsBaseChang
e S α) (β : N →ₗ[R] Q)   (f : M →ₗ[R] N), ↑R ((j.linearMapLeftRightHom β) f) ∘ₗ 
α = β ∘ₗ f
参数：j : IsBaseChange S α；β : N →ₗ[R] Q；f : M →ₗ[R] N；(j.linearMapLeftRightHom β) 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBaseChange.linearMapLeftRightHom_comp_apply`：∀ {R : Type u_1} [inst : 
CommSemiring R] {S : Type u_2} [inst_1 : CommSemiring S] [inst_2 : Algebra R S] 
{M : Type u_3}   [inst_3 : AddCommM…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem linearMapLeftRightHom_comp
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (β : N →ₗ[R] Q) (f : M →ₗ[R] N) :
    (linearMapLeftRightHom j β f).restrictScalars R ∘ₗ α = β ∘ₗ f := by
  ext; simp [linearMapLeftRightHom_comp_apply]

variable [Free R M] [Module.Finite R M]
/-
**IsBaseChange.linearMapLeftRight** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：linearMapLeftRight {α : M ->ₗ[R] P} (j : IsBaseChange S α) {β : N ->ₗ[R] Q
} (k : IsBaseChange S β) : IsBaseChange S (linearMapLeftRightHom j β)
参数：j : IsBaseChange S α；k : IsBaseChange S β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsBaseChange.linearMapRight`：linearMapRight {ε : N ->ₗ[R] P} (ibc : IsBa
seChange S ε) : IsBaseChange S (LinearMap.compRight (M
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearEquiv.arrowCongrAddEquiv_apply`：∀ {R₁ : Type u_9} {R₂ : Type u_10}
 {R₁' : Type u_11} {R₂' : Type u_12} {M₁ : Type u_13} {M₂ : Type u_14}   {M₁' : 
Type u_15} {M₂' : Type u_1…
· 使用定理 `IsBaseChange.linearMapLeftRightHom_apply`：linearMapLeftRightHom_apply {α
 : M ->ₗ[R] P} (j : IsBaseChange S α) (β : N ->ₗ[R] Q) (f : M ->ₗ[R] N) (p : P) 
: linearMapLeftRightHom j β f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearMapLeftRight {α : M →ₗ[R] P} (j : IsBaseChange S α)
    {β : N →ₗ[R] Q} (k : IsBaseChange S β) :
    IsBaseChange S (linearMapLeftRightHom j β) := by
  apply of_equiv <|
      (k.linearMapRight M).equiv ≪≫ₗ liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft Q S j.equiv
  intro f
  ext p
  simp [IsBaseChange.equiv_tmul, LinearEquiv.congrLeft, linearMapLeftRightHom_apply]

end LinearMapLeftRight

section End

variable {S M}
  [Module S P] [IsScalarTower R S P]

/-- The base change map for endomorphisms of a free finite module. -/
/-
**IsBaseChange.endHom** 是 Mathlib 中的一个定义，位于命名空间 `IsBaseChange`。
形式化陈述：endHom {α : M ->ₗ[R] P} (j : IsBaseChange S α) : (M ->ₗ[R] M) ->ₗ[R] (P ->
ₗ[S] P)
参数：j : IsBaseChange S α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base change map for endomorphisms of a free finite module.
-/
noncomputable def endHom {α : M →ₗ[R] P} (j : IsBaseChange S α) :
    (M →ₗ[R] M) →ₗ[R] (P →ₗ[S] P) :=
  ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S ⊗[R] M) P).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R α (M := M))
/-
**IsBaseChange.endHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：endHom_apply {α : M ->ₗ[R] P} (j : IsBaseChange S α) (f : M ->ₗ[R] M) (p :
 P) : endHom j f p = ((liftBaseChangeEquiv S) (α ∘ₗ f)) (j.equiv.symm p)
参数：j : IsBaseChange S α；f : M ->ₗ[R] M；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
theorem endHom_apply
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (f : M →ₗ[R] M) (p : P) :
    endHom j f p = ((liftBaseChangeEquiv S) (α ∘ₗ f)) (j.equiv.symm p) := by
  rfl
/-
**IsBaseChange.endHom_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：endHom_comp_apply {α : M ->ₗ[R] P} (j : IsBaseChange S α) (f : M ->ₗ[R] M)
 (m : M) : endHom j f (α m) = α (f m)
参数：j : IsBaseChange S α；f : M ->ₗ[R] M；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsBaseChange.endHom_apply`：endHom_apply {α : M ->ₗ[R] P} (j : IsBaseChan
ge S α) (f : M ->ₗ[R] M) (p : P) : endHom j f p = ((liftBaseChangeEquiv S) (α ∘ₗ
 f)) (j.equiv.s…
· 使用定理 `IsBaseChange.equiv_symm_apply`：IsBaseChange.equiv_symm_apply (m : M) : h
.equiv.symm (f m) = 1 otimesₜ m
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem endHom_comp_apply
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (f : M →ₗ[R] M) (m : M) :
    endHom j f (α m) = α (f m) := by
  simp [endHom_apply, IsBaseChange.equiv_symm_apply]
/-
**IsBaseChange.endHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：endHom_comp {α : M ->ₗ[R] P} (j : IsBaseChange S α) (f : M ->ₗ[R] M) : (en
dHom j f).restrictScalars R ∘ₗ α = α ∘ₗ f
参数：j : IsBaseChange S α；f : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBaseChange.endHom_comp_apply`：endHom_comp_apply {α : M ->ₗ[R] P} (j : 
IsBaseChange S α) (f : M ->ₗ[R] M) (m : M) : endHom j f (α m) = α (f m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem endHom_comp
    {α : M →ₗ[R] P} (j : IsBaseChange S α) (f : M →ₗ[R] M) :
    (endHom j f).restrictScalars R ∘ₗ α = α ∘ₗ f := by
  ext; simp [endHom_comp_apply]
/-
**IsBaseChange.endHom_one** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：endHom_one {α : M ->ₗ[R] P} (j : IsBaseChange S α) : j.endHom 1 = 1
参数：j : IsBaseChange S α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsBaseChange.inductionOn`：∀ {R : Type u_1} {M : Type v₁} {N : Type v₂} {
S : Type v₃} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : Com
mSemiring R] […
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsBaseChange.endHom_comp_apply`：endHom_comp_apply {α : M ->ₗ[R] P} (j : 
IsBaseChange S α) (f : M ->ₗ[R] M) (m : M) : endHom j f (α m) = α (f m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem endHom_one {α : M →ₗ[R] P} (j : IsBaseChange S α) :
    j.endHom 1 = 1 := by
  ext p
  induction p using j.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul _ _ h => simp [h]
  | tmul m => simp [endHom_comp_apply]

variable [Free R M] [Module.Finite R M]
/-
**IsBaseChange._root_.IsBaseChange.end** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsBaseChange.end {α : M →ₗ[R] P} (j : IsBaseChange S α) :
    IsBaseChange S (endHom j) := by
  apply of_equiv <|
      (j.linearMapRight M).equiv ≪≫ₗ liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft P S j.equiv
  intro f
  ext p
  simp [equiv_tmul, LinearEquiv.congrLeft, endHom_apply]

end End

section Matrix

variable {Q : Type*} [AddCommMonoid Q] [Module R Q] [Module S P] [IsScalarTower R S P]
  [Module S Q] [IsScalarTower R S Q]
  {α : M →ₗ[R] P} {β : N →ₗ[R] Q}
  (ibcM : IsBaseChange S α) (ibcN : IsBaseChange S β)
  {ι θ : Type*} [DecidableEq ι] [Fintype ι] [Finite θ]
  (b : Module.Basis ι R M) (c : Module.Basis θ R N)

/-
**IsBaseChange.linearMapLeftRightHom_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseC
hange`。
形式化陈述：linearMapLeftRightHom_toMatrix (f : M ->ₗ[R] N) : (linearMapLeftRightHom i
bcM β f).toMatrix (ibcM.basis b) (ibcN.basis c) = (f.toMatrix b c).map (algebraM
ap R S)
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsBaseChange.basis_apply`：basis_apply (i) : ibc.basis b i = ε (b i)
· 使用定理 `IsBaseChange.linearMapLeftRightHom_comp_apply`：∀ {R : Type u_1} [inst : 
CommSemiring R] {S : Type u_2} [inst_1 : CommSemiring S] [inst_2 : Algebra R S] 
{M : Type u_3}   [inst_3 : AddCommM…
· 使用定理 `IsBaseChange.basis_repr_comp_apply`：basis_repr_comp_apply (v i) : (ibc.b
asis b).repr (ε v) i = algebraMap R S (b.repr v i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linearMapLeftRightHom_toMatrix (f : M →ₗ[R] N) :
    (linearMapLeftRightHom ibcM β f).toMatrix (ibcM.basis b) (ibcN.basis c) =
      (f.toMatrix b c).map (algebraMap R S) := by
  ext i j
  simp only [toMatrix_apply, Matrix.map_apply, basis_apply,
    linearMapLeftRightHom_comp_apply, basis_repr_comp_apply]
/-
**IsBaseChange.endHom_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：endHom_toMatrix (f : M ->ₗ[R] M) : (endHom ibcM f).toMatrix (ibcM.basis b)
 (ibcM.basis b) = (f.toMatrix b b).map (algebraMap R S)
参数：f : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsBaseChange.basis_apply`：basis_apply (i) : ibc.basis b i = ε (b i)
· 使用定理 `IsBaseChange.endHom_comp_apply`：endHom_comp_apply {α : M ->ₗ[R] P} (j : 
IsBaseChange S α) (f : M ->ₗ[R] M) (m : M) : endHom j f (α m) = α (f m)
· 使用定理 `IsBaseChange.basis_repr_comp_apply`：basis_repr_comp_apply (v i) : (ibc.b
asis b).repr (ε v) i = algebraMap R S (b.repr v i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem endHom_toMatrix (f : M →ₗ[R] M) :
    (endHom ibcM f).toMatrix (ibcM.basis b) (ibcM.basis b) =
      (f.toMatrix b b).map (algebraMap R S) := by
  ext i j
  simp only [toMatrix_apply, Matrix.map_apply]
  simp only [basis_apply, endHom_comp_apply, basis_repr_comp_apply]


end Matrix

section determinant

variable {R : Type*} [CommRing R]
    (S : Type*) [CommRing S] [Algebra R S]
    (M : Type*) [AddCommGroup M] [Module R M]
    {P : Type*} [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

variable [Free R M] [Module.Finite R M]

/-
**IsBaseChange.det_endHom** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：det_endHom {α : M ->ₗ[R] P} (j : IsBaseChange S α) (f : M ->ₗ[R] M) : Line
arMap.det (endHom j f) = algebraMap R S (LinearMap.det f)
参数：j : IsBaseChange S α；f : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `Subsingleton.eq_one`：Subsingleton.eq_one [One α] [Subsingleton α] (a : α
) : a = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBaseChange.endHom_one`：endHom_one {α : M ->ₗ[R] P} (j : IsBaseChange S
 α) : j.endHom 1 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.det_toMatrix`：det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) 
: Matrix.det (toMatrix b b f) = LinearMap.det f
· 使用定理 `IsBaseChange.endHom_toMatrix`：endHom_toMatrix (f : M ->ₗ[R] M) : (endHom
 ibcM f).toMatrix (ibcM.basis b) (ibcM.basis b) = (f.toMatrix b b).map (algebraM
ap R S)
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
-/
theorem det_endHom {α : M →ₗ[R] P} (j : IsBaseChange S α) (f : M →ₗ[R] M) :
    LinearMap.det (endHom j f) = algebraMap R S (LinearMap.det f) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : f = 1 := by
      have : Subsingleton M := Module.subsingleton R M
      exact Subsingleton.eq_one f
    simp [this, endHom_one]
  let b := Module.finBasis R M
  rw [← f.det_toMatrix b, ← (j.endHom f).det_toMatrix (j.basis b),
    endHom_toMatrix, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

end determinant

end IsBaseChange

