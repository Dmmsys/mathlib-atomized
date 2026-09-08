/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Data.DFinsupp.Submonoid
public import Mathlib.Data.DFinsupp.Sigma
public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Properties of the module `Π₀ i, M i`

Given an indexed collection of `R`-modules `M i`, the `R`-module structure on `Π₀ i, M i`
is defined in `Mathlib/Data/DFinsupp/Module.lean`.

In this file we define `LinearMap` versions of various maps:

* `DFinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `DFinsupp.single a` as a linear map;

* `DFinsupp.lmk s : (Π i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i`: `DFinsupp.mk` as a linear map;

* `DFinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `fun f ↦ f i` as a linear map;

* `DFinsupp.lsum`: `DFinsupp.sum` or `DFinsupp.liftAddHom` as a `LinearMap`.

## Implementation notes

This file should try to mirror `LinearAlgebra.Finsupp` where possible. The API of `Finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

open Module

variable {ι ι' : Type*} {R : Type*} {S : Type*} {M : ι → Type*} {N : Type*}

namespace DFinsupp

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [AddCommMonoid N] [Module R N]

section DecidableEq
variable [DecidableEq ι]

/-- `DFinsupp.mk` as a `LinearMap`. -/
/-
**DFinsupp.lmk** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：lmk (s : Finset ι) : (forall i : (↑s : Set ι), M i) ->ₗ[R] Π₀ i, M i where
 toFun
参数：s : Finset ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.mk` as a `LinearMap`.
-/
def lmk (s : Finset ι) : (∀ i : (↑s : Set ι), M i) →ₗ[R] Π₀ i, M i where
  toFun := mk s
  map_add' _ _ := mk_add
  map_smul' c x := mk_smul c x

/-- `DFinsupp.single` as a `LinearMap` -/
/-
**DFinsupp.lsingle** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：lsingle (i) : M i ->ₗ[R] Π₀ i, M i
参数：i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.single` as a `LinearMap`
-/
def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
  { DFinsupp.singleAddHom _ _ with
    toFun := single i
    map_smul' := single_smul }

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere. -/
/-
**DFinsupp.lhom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lhom_ext ⦃φ ψ : (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i x, φ (single i x) = ψ 
(single i x)) : φ = ψ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toAddMonoidHom_injective`：toAddMonoidHom_injective : Function.
Injective (toAddMonoidHom : (M ->ₛₗ[σ] M₃) -> M ->+ M₃)
· 使用定理 `DFinsupp.addHom_ext`：addHom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀
 i, β i) ->+ γ⦄ (H : forall (i : ι) (y : β i), f (single i y) = g (single i y)) 
: f = g

--- 原说明 ---
Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree ever
ywhere.
-/
theorem lhom_ext ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i x, φ (single i x) = ψ (single i x)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

See note [partially-applied ext lemmas].
After applying this lemma, if `M = R` then it suffices to verify
`φ (single a 1) = ψ (single a 1)`. -/
@[ext 1100]
/-
**DFinsupp.lhom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lhom_ext' ⦃φ ψ : (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i, φ.comp (lsingle i) =
 ψ.comp (lsingle i)) : φ = ψ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lhom_ext`：lhom_ext ⦃φ ψ : (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i x
, φ (single i x) = ψ (single i x)) : φ = ψ
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…

--- 原说明 ---
Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree ever
ywhere.

See note [partially-applied ext lemmas].
After applying this lemma, if `M = R` then it suffices to verify
`φ (single a 1) = ψ (single a 1)`.
-/
theorem lhom_ext' ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄ (h : ∀ i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
    φ = ψ :=
  lhom_ext fun i => LinearMap.congr_fun (h i)
/-
**DFinsupp.lmk_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lmk_apply (s : Finset ι) (x) : (lmk s : _ ->ₗ[R] Π₀ i, M i) x = mk s x
参数：s : Finset ι；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lmk_apply (s : Finset ι) (x) : (lmk s : _ →ₗ[R] Π₀ i, M i) x = mk s x :=
  rfl

@[simp]
/-
**DFinsupp.lsingle_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lsingle_apply (i : ι) (x : M i) : (lsingle i : (M i) ->ₗ[R] _) x = single 
i x
参数：i : ι；x : M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lsingle_apply (i : ι) (x : M i) : (lsingle i : (M i) →ₗ[R] _) x = single i x :=
  rfl

end DecidableEq

/-- Interpret `fun (f : Π₀ i, M i) ↦ f i` as a linear map. -/
/-
**DFinsupp.lapply** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：lapply (i : ι) : (Π₀ i, M i) ->ₗ[R] M i where toFun f
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret `fun (f : Π₀ i, M i) ↦ f i` as a linear map.
-/
def lapply (i : ι) : (Π₀ i, M i) →ₗ[R] M i where
  toFun f := f i
  map_add' f g := add_apply f g i
  map_smul' c f := smul_apply c f i

@[simp]
/-
**DFinsupp.lapply_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : (Π₀ i, M i) ->ₗ[R] _) f
 = f i
参数：i : ι；f : Π₀ i, M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : (Π₀ i, M i) →ₗ[R] _) f = f i :=
  rfl
/-
**DFinsupp.injective_pi_lapply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：injective_pi_lapply : Function.Injective (LinearMap.pi (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem injective_pi_lapply : Function.Injective (LinearMap.pi (R := R) <| lapply (M := M)) :=
  fun _ _ h ↦ ext fun _ ↦ congr_fun h _

@[simp]
/-
**DFinsupp.lapply_comp_lsingle_same** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lapply_comp_lsingle_same [DecidableEq ι] (i : ι) : lapply i ∘ₗ lsingle i =
 (.id : M i ->ₗ[R] M i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
theorem lapply_comp_lsingle_same [DecidableEq ι] (i : ι) :
    lapply i ∘ₗ lsingle i = (.id : M i →ₗ[R] M i) := by ext; simp

@[simp]
/-
**DFinsupp.lapply_comp_lsingle_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lapply_comp_lsingle_of_ne [DecidableEq ι] (i i' : ι) (h : i != i') : lappl
y i ∘ₗ lsingle i' = (0 : M i' ->ₗ[R] M i)
参数：i i' : ι；h : i != i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lapply_comp_lsingle_of_ne [DecidableEq ι] (i i' : ι) (h : i ≠ i') :
    lapply i ∘ₗ lsingle i' = (0 : M i' →ₗ[R] M i) := by ext; simp [h.symm]

section Lsum

variable (S)
variable [DecidableEq ι]

/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)
    [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] :
    EquivLike (LinearEquiv σ M M₂) M M₂ :=
  inferInstance

/-- `DFinsupp.equivCongrLeft` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.domLCongr`. -/
@[simps! apply]
/-
**DFinsupp.domLCongr** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：domLCongr (e : ι ≃ ι') : (Π₀ i, M i) ≃ₗ[R] (Π₀ i, M (e.symm i)) where __
参数：e : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`DFinsupp.equivCongrLeft` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.domLCongr`.
-/
def domLCongr (e : ι ≃ ι') : (Π₀ i, M i) ≃ₗ[R] (Π₀ i, M (e.symm i)) where
  __ := DFinsupp.equivCongrLeft e
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- `DFinsupp.sigmaCurryEquiv` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.curryLinearEquiv`. -/
@[simps! apply symm_apply]
/-
**DFinsupp.sigmaCurryLEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：sigmaCurryLEquiv {α : ι -> Type*} {M : (i : ι) -> α i -> Type*} [Π i j, Ad
dCommMonoid (M i j)] [Π i j, Module R (M i j)] : (Π₀ (i : (x : ι) × α x), M i.fs
t i.snd) ≃ₗ[R] Π₀ (i : ι) (j : α i), M i j where __
参数：i : ι；M i j；M i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.sigmaCurryEquiv` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.curryLinearEquiv`.
-/
def sigmaCurryLEquiv {α : ι → Type*} {M : (i : ι) → α i → Type*}
    [Π i j, AddCommMonoid (M i j)] [Π i j, Module R (M i j)] :
    (Π₀ (i : (x : ι) × α x), M i.fst i.snd) ≃ₗ[R] Π₀ (i : ι) (j : α i), M i j where
  __ := DFinsupp.sigmaCurryEquiv
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- `DFinsupp.equivFunOnFintype` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.linearEquivFunOnFintype`. -/
@[simps! apply symm_apply]
/-
**DFinsupp.linearEquivFunOnFintype** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：linearEquivFunOnFintype [Fintype ι] : (Π₀ i, M i) ≃ₗ[R] (Π i, M i) where _
_
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.equivFunOnFintype` as a linear equivalence.

This is the `DFinsupp` version of `Finsupp.linearEquivFunOnFintype`.
-/
def linearEquivFunOnFintype [Fintype ι] : (Π₀ i, M i) ≃ₗ[R] (Π i, M i) where
  __ := equivFunOnFintype
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `DFinsupp` version of `Finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
/-
**DFinsupp.lsum** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：lsum [Semiring S] [Module S N] [SMulCommClass R S N] : (forall i, M i ->ₗ[
R] N) ≃ₗ[S] (Π₀ i, M i) ->ₗ[R] N where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `DFinsupp` version of `Finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semiri
ngs are used.
-/
def lsum [Semiring S] [Module S N] [SMulCommClass R S N] :
    (∀ i, M i →ₗ[R] N) ≃ₗ[S] (Π₀ i, M i) →ₗ[R] N where
  toFun F :=
    { toFun := sumAddHom fun i => (F i).toAddMonoidHom
      map_add' := (DFinsupp.liftAddHom fun (i : ι) => (F i).toAddMonoidHom).map_add
      map_smul' := fun c f => by
        dsimp
        apply DFinsupp.induction f
        · rw [smul_zero, map_zero, smul_zero]
        · intro a b f _ _ hf
          rw [smul_add, map_add, map_add, smul_add, hf, ← single_smul,
            sumAddHom_single, sumAddHom_single, LinearMap.toAddMonoidHom_coe,
            map_smul] }
  invFun F i := F.comp (lsingle i)
  left_inv F := by
    ext
    simp
  right_inv F := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
  map_add' F G := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp
  map_smul' c F := by
    refine DFinsupp.lhom_ext' (fun i ↦ ?_)
    ext
    simp

/-- While `simp` can prove this, it is often convenient to avoid unfolding `lsum` into `sumAddHom`
with `DFinsupp.lsum_apply_apply`. -/
/-
**DFinsupp.lsum_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lsum_single [Semiring S] [Module S N] [SMulCommClass R S N] (F : forall i,
 M i ->ₗ[R] N) (i) (x : M i) : lsum S F (single i x) = F i x
参数：F : forall i, M i ->ₗ[R] N；i；x : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
While `simp` can prove this, it is often convenient to avoid unfolding `lsum` in
to `sumAddHom`
with `DFinsupp.lsum_apply_apply`.
-/
theorem lsum_single [Semiring S] [Module S N] [SMulCommClass R S N] (F : ∀ i, M i →ₗ[R] N) (i)
    (x : M i) : lsum S F (single i x) = F i x := by
  simp
/-
**DFinsupp.lsum_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：lsum_lsingle [Semiring S] [forall i, Module S (M i)] [forall i, SMulCommCl
ass R S (M i)] : lsum S (lsingle (R
参数：M i；M i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lhom_ext`：lhom_ext ⦃φ ψ : (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i x
, φ (single i x) = ψ (single i x)) : φ = ψ
· 使用定理 `DFinsupp.lsum_single`：lsum_single [Semiring S] [Module S N] [SMulCommCla
ss R S N] (F : forall i, M i ->ₗ[R] N) (i) (x : M i) : lsum S F (single i x) = F
 i x
-/
theorem lsum_lsingle [Semiring S] [∀ i, Module S (M i)] [∀ i, SMulCommClass R S (M i)] :
    lsum S (lsingle (R := R) (M := M)) = .id :=
  lhom_ext (lsum_single _ _)
/-
**DFinsupp.iSup_range_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：iSup_range_lsingle : ⨆ i, LinearMap.range (lsingle (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
· 使用定理 `DFinsupp.lsum_lsingle`：lsum_lsingle [Semiring S] [forall i, Module S (M 
i)] [forall i, SMulCommClass R S (M i)] : lsum S (lsingle (R
· 使用定理 `dfinsuppSumAddHom_mem`：dfinsuppSumAddHom_mem [forall i, AddZeroClass (β 
i)] [AddCommMonoid γ] {S : Type*} [SetLike S γ] [AddSubmonoidClass S γ] (s : S) 
(f : Π₀ i, …
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
-/
theorem iSup_range_lsingle : ⨆ i, LinearMap.range (lsingle (R := R) (M := M) i) = ⊤ :=
  top_le_iff.mp fun m _ ↦ by
    rw [← LinearMap.id_apply (R := R) m, ← lsum_lsingle ℕ]
    exact dfinsuppSumAddHom_mem _ _ _ fun i _ ↦ Submodule.mem_iSup_of_mem i ⟨_, rfl⟩

end Lsum

/-! ### Bundled versions of `DFinsupp.mapRange`

The names should match the equivalent bundled `Finsupp.mapRange` definitions.
-/

section mapRange
variable {β β₁ β₂ : ι → Type*}

section AddCommMonoid
variable [∀ i, AddCommMonoid (β i)] [∀ i, AddCommMonoid (β₁ i)] [∀ i, AddCommMonoid (β₂ i)]
variable [∀ i, Module R (β i)] [∀ i, Module R (β₁ i)] [∀ i, Module R (β₂ i)]

set_option backward.isDefEq.respectTransparency false in
/-
**DFinsupp.mker_mapRangeAddMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：mker_mapRangeAddMonoidHom (f : forall i, β₁ i ->+ β₂ i) : AddMonoidHom.mke
r (mapRange.addMonoidHom f) = (AddSubmonoid.pi Set.univ (fun i => AddMonoidHom.m
ker (f i))).comap coeFnAddMonoidHom
参数：f : forall i, β₁ i ->+ β₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.ext`：∀ {M : Type u_1} [inst : AddZeroClass M] {S T : AddSub
monoid M}, (∀ (x : M), x ∈ S ↔ x ∈ T) → S = T
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.mapRange.addMonoidHom_apply`：∀ {ι : Type u} {β₁ : ι → Type v₁} 
{β₂ : ι → Type v₂} [inst : (i : ι) → AddZeroClass (β₁ i)]   [inst_1 : (i : ι) → 
AddZeroClass (β₂ i)] (f : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mker_mapRangeAddMonoidHom (f : ∀ i, β₁ i →+ β₂ i) :
    AddMonoidHom.mker (mapRange.addMonoidHom f) =
      (AddSubmonoid.pi Set.univ (fun i ↦ AddMonoidHom.mker (f i))).comap coeFnAddMonoidHom := by
  ext
  simp [AddSubmonoid.pi, DFinsupp.ext_iff]
/-
**DFinsupp.mrange_mapRangeAddMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：mrange_mapRangeAddMonoidHom (f : forall i, β₁ i ->+ β₂ i) : AddMonoidHom.m
range (mapRange.addMonoidHom f) = (AddSubmonoid.pi Set.univ (fun i => AddMonoidH
om.mrange (f i))).comap coeFnAddMonoidHom
参数：f : forall i, β₁ i ->+ β₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.ext`：∀ {M : Type u_1} [inst : AddZeroClass M] {S T : AddSub
monoid M}, (∀ (x : M), x ∈ S ↔ x ∈ T) → S = T
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.mapRange.addMonoidHom_apply`：∀ {ι : Type u} {β₁ : ι → Type v₁} 
{β₂ : ι → Type v₂} [inst : (i : ι) → AddZeroClass (β₁ i)]   [inst_1 : (i : ι) → 
AddZeroClass (β₂ i)] (f : …
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.mk_of_mem`：mk_of_mem (hi : i in s) : (mk s x : forall i, β i) i
 = x ⟨i, hi⟩
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.notMem_support_iff`：notMem_support_iff {f : Π₀ i, β i} {i : ι} 
: i ∉ f.support ↔ f i = 0
· 使用定理 `DFinsupp.mk_of_notMem`：mk_of_notMem (hi : i ∉ s) : (mk s x : forall i, β
 i) i = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma mrange_mapRangeAddMonoidHom (f : ∀ i, β₁ i →+ β₂ i) :
    AddMonoidHom.mrange (mapRange.addMonoidHom f) =
      (AddSubmonoid.pi Set.univ (fun i ↦ AddMonoidHom.mrange (f i))).comap coeFnAddMonoidHom := by
  classical
  ext x
  simp only [AddSubmonoid.mem_comap, coeFnAddMonoidHom_apply]
  refine ⟨fun ⟨y, hy⟩ i hi ↦ ?_, fun h ↦ ?_⟩
  · simp [← hy]
  · choose g hg using fun i => h i (Set.mem_univ _)
    use DFinsupp.mk x.support (g ·)
    ext i
    simp only [Finset.coe_sort_coe, mapRange.addMonoidHom_apply, mapRange_apply]
    by_cases mem : i ∈ x.support
    · rw [mk_of_mem mem, hg]
    · rw [DFinsupp.notMem_support_iff.mp mem, mk_of_notMem mem, map_zero]
/-
**DFinsupp.mapRange_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mapRange_smul (f : forall i, β₁ i -> β₂ i) (hf : forall i, f i 0 = 0) (r :
 R) (hf' : forall i x, f i (r • x) = r • f i x) (g : Π₀ i, β₁ i) : mapRange f hf
 (r • g) = r • mapRange f hf g
参数：f : forall i, β₁ i -> β₂ i；hf : forall i, f i 0 = 0；r : R；hf' : forall i x, f
 i (r • x) = r • f i x；g : Π₀ i, β₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange_smul (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (r : R)
    (hf' : ∀ i x, f i (r • x) = r • f i x) (g : Π₀ i, β₁ i) :
    mapRange f hf (r • g) = r • mapRange f hf g := by
  ext
  simp only [mapRange_apply f, coe_smul, Pi.smul_apply, hf']

/-- `DFinsupp.mapRange` as a `LinearMap`. -/
@[simps! apply]
/-
**DFinsupp.mapRange.linearMap** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.mapRange`。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     [inst : Semiring R] →       {β₁ : 
ι → Type u_8} →         {β₂ : ι → Type u_9} →           [inst_1 : (i : ι) → AddC
ommMonoid (β₁ i)] →             [inst_2 : (i : ι) → AddCommMonoid (β₂ i)] →     
          [inst_3 : (i : ι) → _root_.Module R (β₁ i)] →                 [inst_4 
: (i : ι) → _root_.Module R (β₂ i)] →                   ((i : ι) → β₁ i →ₗ[R] β₂
 i) → (Π₀ (i : ι), β₁ i) →ₗ[R] Π₀ (i : ι), β₂ i
参数：i : ι；β₁ i；i : ι；β₂ i；i : ι；β₁ i；i : ι；β₂ i；(i : ι) → β₁ i →ₗ[R] β₂ i；Π₀ (i :
 ι), β₁ i；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.mapRange` as a `LinearMap`.
-/
def mapRange.linearMap (f : ∀ i, β₁ i →ₗ[R] β₂ i) : (Π₀ i, β₁ i) →ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addMonoidHom fun i => (f i).toAddMonoidHom with
    toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
    map_smul' := fun r => mapRange_smul _ (fun i => (f i).map_zero) _ fun i => (f i).map_smul r }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**DFinsupp.mapRange.linearMap_id** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.mapRange`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} [inst : Semiring R] {β₂ : ι → Type u_9} [i
nst_1 : (i : ι) → AddCommMonoid (β₂ i)]   [inst_2 : (i : ι) → _root_.Module R (β
₂ i)], (DFinsupp.mapRange.linearMap fun i => LinearMap.id) = LinearMap.id
参数：i : ι；β₂ i；i : ι；β₂ i；DFinsupp.mapRange.linearMap fun i => LinearMap.id。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange.linearMap_id :
    (mapRange.linearMap fun i => (LinearMap.id : β₂ i →ₗ[R] _)) = LinearMap.id := by
  ext
  simp [linearMap]
/-
**DFinsupp.mapRange.linearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.mapRange`
。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} [inst : Semiring R] {β : ι → Type u_7} {β₁
 : ι → Type u_8} {β₂ : ι → Type u_9}   [inst_1 : (i : ι) → AddCommMonoid (β i)] 
[inst_2 : (i : ι) → AddCommMonoid (β₁ i)]   [inst_3 : (i : ι) → AddCommMonoid (β
₂ i)] [inst_4 : (i : ι) → _root_.Module R (β i)]   [inst_5 : (i : ι) → _root_.Mo
dule R (β₁ i)] [inst_6 : (i : ι) → _root_.Module R (β₂ i)]   (f : (i : ι) → β₁ i
 →ₗ[R] β₂ i) (f₂ : (i : ι) → β i →ₗ[R] β₁ i),   (DFinsupp.mapRange.linearMap fun
 i => f i ∘ₗ f₂ i) = DFinsupp.mapRange.linearMap f ∘ₗ DFinsupp.mapRange.linearMa
p f₂
参数：i : ι；β i；i : ι；β₁ i；i : ι；β₂ i；i : ι；β i；i : ι；β₁ i；i : ι；β₂ i；f : (i : ι) →
 β₁ i →ₗ[R] β₂ i；f₂ : (i : ι) → β i →ₗ[R] β₁ i；DFinsupp.mapRange.linearMap fun i
 => f i ∘ₗ f₂ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DFinsupp.mapRange_comp`：mapRange_comp (f : forall i, β₁ i -> β₂ i) (f₂ :
 forall i, β i -> β₁ i) (hf : forall i, f i 0 = 0) (hf₂ : forall i, f₂ i 0 = 0) 
(h : forall …
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
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
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mapRange.linearMap_comp (f : ∀ i, β₁ i →ₗ[R] β₂ i) (f₂ : ∀ i, β i →ₗ[R] β₁ i) :
    (mapRange.linearMap fun i => (f i).comp (f₂ i)) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
  LinearMap.ext <| mapRange_comp (fun i x => f i x) (fun i x => f₂ i x)
    (fun i => (f i).map_zero) (fun i => (f₂ i).map_zero) (by simp)
/-
**DFinsupp.sum_mapRange_index.linearMap** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.sum_
mapRange_index`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {N : Type u_6} [inst : Semiring R] [inst_1
 : AddCommMonoid N]   [inst_2 : _root_.Module R N] {β₁ : ι → Type u_8} {β₂ : ι →
 Type u_9} [inst_3 : (i : ι) → AddCommMonoid (β₁ i)]   [inst_4 : (i : ι) → AddCo
mmMonoid (β₂ i)] [inst_5 : (i : ι) → _root_.Module R (β₁ i)]   [inst_6 : (i : ι)
 → _root_.Module R (β₂ i)] [inst_7 : DecidableEq ι] {f : (i : ι) → β₁ i →ₗ[R] β₂
 i}   {h : (i : ι) → β₂ i →ₗ[R] N} {l : Π₀ (i : ι), β₁ i},   ((DFinsupp.lsum ℕ) 
h) ((DFinsupp.mapRange.linearMap f) l) = ((DFinsupp.lsum ℕ) fun i => h i ∘ₗ f i)
 l
参数：i : ι；β₁ i；i : ι；β₂ i；i : ι；β₁ i；i : ι；β₂ i；i : ι；i : ι；i : ι；(DFinsupp.lsum 
ℕ) h；(DFinsupp.mapRange.linearMap f) l；(DFinsupp.lsum ℕ) fun i => h i ∘ₗ f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.mapRange.linearMap_apply`：∀ {ι : Type u_1} {R : Type u_3} [inst
 : Semiring R] {β₁ : ι → Type u_8} {β₂ : ι → Type u_9}   [inst_1 : (i : ι) → Add
CommMonoid (β₁ i)] [ins…
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `DFinsupp.sum_mapRange_index`：∀ {ι : Type u} {γ : Type w} [inst : Decidab
leEq ι] {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}   [inst_1 : (i : ι) → Zero (β₁ i)]
 [inst_2 : (i : ι…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
-/
theorem sum_mapRange_index.linearMap [DecidableEq ι] {f : ∀ i, β₁ i →ₗ[R] β₂ i}
    {h : ∀ i, β₂ i →ₗ[R] N} {l : Π₀ i, β₁ i} :
    DFinsupp.lsum ℕ h (mapRange.linearMap f l) = DFinsupp.lsum ℕ (fun i => (h i).comp (f i)) l := by
  classical simpa [DFinsupp.sumAddHom_apply] using! sum_mapRange_index fun i => by simp
/-
**DFinsupp.ker_mapRangeLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：ker_mapRangeLinearMap (f : forall i, β₁ i ->ₗ[R] β₂ i) : LinearMap.ker (ma
pRange.linearMap f) = (Submodule.pi Set.univ (fun i => LinearMap.ker (f i))).com
ap (coeFnLinearMap R)
参数：f : forall i, β₁ i ->ₗ[R] β₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.toAddSubmonoid_injective`：toAddSubmonoid_injective : Injective
 (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
· 使用引理 `DFinsupp.mker_mapRangeAddMonoidHom`：mker_mapRangeAddMonoidHom (f : foral
l i, β₁ i ->+ β₂ i) : AddMonoidHom.mker (mapRange.addMonoidHom f) = (AddSubmonoi
d.pi Set.univ (fun i => …
-/
lemma ker_mapRangeLinearMap (f : ∀ i, β₁ i →ₗ[R] β₂ i) :
    LinearMap.ker (mapRange.linearMap f) =
      (Submodule.pi Set.univ (fun i ↦ LinearMap.ker (f i))).comap (coeFnLinearMap R) :=
  Submodule.toAddSubmonoid_injective <| mker_mapRangeAddMonoidHom (f · |>.toAddMonoidHom)
/-
**DFinsupp.range_mapRangeLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：range_mapRangeLinearMap (f : forall i, β₁ i ->ₗ[R] β₂ i) : LinearMap.range
 (mapRange.linearMap f) = (Submodule.pi Set.univ (LinearMap.range <| f ·)).comap
 (coeFnLinearMap R)
参数：f : forall i, β₁ i ->ₗ[R] β₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.toAddSubmonoid_injective`：toAddSubmonoid_injective : Injective
 (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
· 使用引理 `DFinsupp.mrange_mapRangeAddMonoidHom`：mrange_mapRangeAddMonoidHom (f : f
orall i, β₁ i ->+ β₂ i) : AddMonoidHom.mrange (mapRange.addMonoidHom f) = (AddSu
bmonoid.pi Set.univ (fun i…
-/
lemma range_mapRangeLinearMap (f : ∀ i, β₁ i →ₗ[R] β₂ i) :
    LinearMap.range (mapRange.linearMap f) =
      (Submodule.pi Set.univ (LinearMap.range <| f ·)).comap (coeFnLinearMap R) :=
  Submodule.toAddSubmonoid_injective <| mrange_mapRangeAddMonoidHom (f · |>.toAddMonoidHom)

/-- `DFinsupp.mapRange.linearMap` as a `LinearEquiv`. -/
@[simps apply]
/-
**DFinsupp.mapRange.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp.mapRange`。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     [inst : Semiring R] →       {β₁ : 
ι → Type u_8} →         {β₂ : ι → Type u_9} →           [inst_1 : (i : ι) → AddC
ommMonoid (β₁ i)] →             [inst_2 : (i : ι) → AddCommMonoid (β₂ i)] →     
          [inst_3 : (i : ι) → _root_.Module R (β₁ i)] →                 [inst_4 
: (i : ι) → _root_.Module R (β₂ i)] →                   ((i : ι) → β₁ i ≃ₗ[R] β₂
 i) → (Π₀ (i : ι), β₁ i) ≃ₗ[R] Π₀ (i : ι), β₂ i
参数：i : ι；β₁ i；i : ι；β₂ i；i : ι；β₁ i；i : ι；β₂ i；(i : ι) → β₁ i ≃ₗ[R] β₂ i；Π₀ (i :
 ι), β₁ i；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.mapRange.linearMap` as a `LinearEquiv`.
-/
def mapRange.linearEquiv (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] Π₀ i, β₂ i :=
  { mapRange.addEquiv fun i => (e i).toAddEquiv,
    mapRange.linearMap fun i => (e i).toLinearMap with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero }

@[simp]
/-
**DFinsupp.mapRange.linearEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.mapRang
e`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} [inst : Semiring R] {β₁ : ι → Type u_8} [i
nst_1 : (i : ι) → AddCommMonoid (β₁ i)]   [inst_2 : (i : ι) → _root_.Module R (β
₁ i)],   (DFinsupp.mapRange.linearEquiv fun i => LinearEquiv.refl R (β₁ i)) = Li
nearEquiv.refl R (Π₀ (i : ι), β₁ i)
参数：i : ι；β₁ i；i : ι；β₁ i；DFinsupp.mapRange.linearEquiv fun i => LinearEquiv.refl
 R (β₁ i)；Π₀ (i : ι), β₁ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `DFinsupp.mapRange_id`：mapRange_id (h : forall i, id (0 : β₁ i) = 0
-/
theorem mapRange.linearEquiv_refl :
    (mapRange.linearEquiv fun i => LinearEquiv.refl R (β₁ i)) = LinearEquiv.refl _ _ :=
  LinearEquiv.ext mapRange_id
/-
**DFinsupp.mapRange.linearEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.mapRan
ge`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} [inst : Semiring R] {β : ι → Type u_7} {β₁
 : ι → Type u_8} {β₂ : ι → Type u_9}   [inst_1 : (i : ι) → AddCommMonoid (β i)] 
[inst_2 : (i : ι) → AddCommMonoid (β₁ i)]   [inst_3 : (i : ι) → AddCommMonoid (β
₂ i)] [inst_4 : (i : ι) → _root_.Module R (β i)]   [inst_5 : (i : ι) → _root_.Mo
dule R (β₁ i)] [inst_6 : (i : ι) → _root_.Module R (β₂ i)] (f : (i : ι) → β i ≃ₗ
[R] β₁ i)   (f₂ : (i : ι) → β₁ i ≃ₗ[R] β₂ i),   (DFinsupp.mapRange.linearEquiv f
un i => f i ≪≫ₗ f₂ i) =     DFinsupp.mapRange.linearEquiv f ≪≫ₗ DFinsupp.mapRang
e.linearEquiv f₂
参数：i : ι；β i；i : ι；β₁ i；i : ι；β₂ i；i : ι；β i；i : ι；β₁ i；i : ι；β₂ i；f : (i : ι) →
 β i ≃ₗ[R] β₁ i；f₂ : (i : ι) → β₁ i ≃ₗ[R] β₂ i；DFinsupp.mapRange.linearEquiv fun
 i => f i ≪≫ₗ f₂ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `DFinsupp.mapRange_comp`：mapRange_comp (f : forall i, β₁ i -> β₂ i) (f₂ :
 forall i, β i -> β₁ i) (hf : forall i, f i 0 = 0) (hf₂ : forall i, f₂ i 0 = 0) 
(h : forall …
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mapRange.linearEquiv_trans (f : ∀ i, β i ≃ₗ[R] β₁ i) (f₂ : ∀ i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
  LinearEquiv.ext <| mapRange_comp (fun i x => f₂ i x) (fun i x => f i x)
    (fun i => (f₂ i).map_zero) (fun i => (f i).map_zero) (by simp)

@[simp]
/-
**DFinsupp.mapRange.linearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp.mapRang
e`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} [inst : Semiring R] {β₁ : ι → Type u_8} {β
₂ : ι → Type u_9}   [inst_1 : (i : ι) → AddCommMonoid (β₁ i)] [inst_2 : (i : ι) 
→ AddCommMonoid (β₂ i)]   [inst_3 : (i : ι) → _root_.Module R (β₁ i)] [inst_4 : 
(i : ι) → _root_.Module R (β₂ i)]   (e : (i : ι) → β₁ i ≃ₗ[R] β₂ i),   (DFinsupp
.mapRange.linearEquiv e).symm = DFinsupp.mapRange.linearEquiv fun i => (e i).sym
m
参数：i : ι；β₁ i；i : ι；β₂ i；i : ι；β₁ i；i : ι；β₂ i；e : (i : ι) → β₁ i ≃ₗ[R] β₂ i；DFi
nsupp.mapRange.linearEquiv e；e i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapRange.linearEquiv_symm (e : ∀ i, β₁ i ≃ₗ[R] β₂ i) :
    (mapRange.linearEquiv e).symm = mapRange.linearEquiv fun i => (e i).symm :=
  rfl

end AddCommMonoid

section AddCommGroup

/-
**DFinsupp.ker_mapRangeAddMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：ker_mapRangeAddMonoidHom [forall i, AddCommGroup (β₁ i)] [forall i, AddCom
mMonoid (β₂ i)] (f : forall i, β₁ i ->+ β₂ i) : (mapRange.addMonoidHom f).ker = 
(AddSubgroup.pi Set.univ (f · |>.ker)).comap coeFnAddMonoidHom
参数：β₁ i；β₂ i；f : forall i, β₁ i ->+ β₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.toAddSubmonoid_injective`：∀ {G : Type u_1} [inst : AddGroup 
G], Function.Injective AddSubgroup.toAddSubmonoid
· 使用引理 `DFinsupp.mker_mapRangeAddMonoidHom`：mker_mapRangeAddMonoidHom (f : foral
l i, β₁ i ->+ β₂ i) : AddMonoidHom.mker (mapRange.addMonoidHom f) = (AddSubmonoi
d.pi Set.univ (fun i => …
-/
lemma ker_mapRangeAddMonoidHom
    [∀ i, AddCommGroup (β₁ i)] [∀ i, AddCommMonoid (β₂ i)] (f : ∀ i, β₁ i →+ β₂ i) :
    (mapRange.addMonoidHom f).ker =
      (AddSubgroup.pi Set.univ (f · |>.ker)).comap coeFnAddMonoidHom :=
  AddSubgroup.toAddSubmonoid_injective <| mker_mapRangeAddMonoidHom f
/-
**DFinsupp.range_mapRangeAddMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：range_mapRangeAddMonoidHom [forall i, AddCommGroup (β₁ i)] [forall i, AddC
ommGroup (β₂ i)] (f : forall i, β₂ i ->+ β₁ i) : (mapRange.addMonoidHom f).range
 = (AddSubgroup.pi Set.univ (f · |>.range)).comap coeFnAddMonoidHom
参数：β₁ i；β₂ i；f : forall i, β₂ i ->+ β₁ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.toAddSubmonoid_injective`：∀ {G : Type u_1} [inst : AddGroup 
G], Function.Injective AddSubgroup.toAddSubmonoid
· 使用引理 `DFinsupp.mrange_mapRangeAddMonoidHom`：mrange_mapRangeAddMonoidHom (f : f
orall i, β₁ i ->+ β₂ i) : AddMonoidHom.mrange (mapRange.addMonoidHom f) = (AddSu
bmonoid.pi Set.univ (fun i…
-/
lemma range_mapRangeAddMonoidHom
    [∀ i, AddCommGroup (β₁ i)] [∀ i, AddCommGroup (β₂ i)] (f : ∀ i, β₂ i →+ β₁ i) :
    (mapRange.addMonoidHom f).range =
      (AddSubgroup.pi Set.univ (f · |>.range)).comap coeFnAddMonoidHom :=
  AddSubgroup.toAddSubmonoid_injective <| mrange_mapRangeAddMonoidHom f

end AddCommGroup

end mapRange

section CoprodMap

variable [DecidableEq ι]

/-- Given a family of linear maps `f i : M i →ₗ[R] N`, we can form a linear map
`(Π₀ i, M i) →ₗ[R] N` which sends `x : Π₀ i, M i` to the sum over `i` of `f i` applied to `x i`.
This is the map coming from the universal property of `Π₀ i, M i` as the coproduct of the `M i`.
See also `LinearMap.coprod` for the binary product version. -/
/-
**DFinsupp.coprodMap** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：coprodMap (f : forall i : ι, M i ->ₗ[R] N) : (Π₀ i, M i) ->ₗ[R] N
参数：f : forall i : ι, M i ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of linear maps `f i : M i →ₗ[R] N`, we can form a linear map
`(Π₀ i, M i) →ₗ[R] N` which sends `x : Π₀ i, M i` to the sum over `i` of `f i` a
pplied to `x i`.
This is the map coming from the universal property of `Π₀ i, M i` as the coprodu
ct of the `M i`.
See also `LinearMap.coprod` for the binary product version.
-/
def coprodMap (f : ∀ i : ι, M i →ₗ[R] N) : (Π₀ i, M i) →ₗ[R] N :=
  (DFinsupp.lsum ℕ fun _ : ι => LinearMap.id) ∘ₗ DFinsupp.mapRange.linearMap f
/-
**DFinsupp.coprodMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：coprodMap_apply [forall x : N, Decidable (x != 0)] (f : forall i : ι, M i 
->ₗ[R] N) (x : Π₀ i, M i) : coprodMap f x = DFinsupp.sum (mapRange (fun i => f i
) (fun _ => map_zero _) x) fun _ => id
参数：x != 0；f : forall i : ι, M i ->ₗ[R] N；x : Π₀ i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
-/
theorem coprodMap_apply [∀ x : N, Decidable (x ≠ 0)] (f : ∀ i : ι, M i →ₗ[R] N) (x : Π₀ i, M i) :
    coprodMap f x =
      DFinsupp.sum (mapRange (fun i => f i) (fun _ => map_zero _) x) fun _ =>
        id :=
  DFinsupp.sumAddHom_apply _ _
/-
**DFinsupp.coprodMap_apply_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：coprodMap_apply_single (f : forall i : ι, M i ->ₗ[R] N) (i : ι) (x : M i) 
: coprodMap f (single i x) = f i x
参数：f : forall i : ι, M i ->ₗ[R] N；i : ι；x : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.mapRange.linearMap_apply`：∀ {ι : Type u_1} {R : Type u_3} [inst
 : Semiring R] {β₁ : ι → Type u_8} {β₂ : ι → Type u_9}   [inst_1 : (i : ι) → Add
CommMonoid (β₁ i)] [ins…
· 使用定理 `DFinsupp.mapRange_single`：mapRange_single {f : forall i, β₁ i -> β₂ i} {
hf : forall i, f i 0 = 0} {i : ι} {b : β₁ i} : mapRange f hf (single i b) = sing
le i (f i b)
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprodMap_apply_single (f : ∀ i : ι, M i →ₗ[R] N) (i : ι) (x : M i) :
    coprodMap f (single i x) = f i x := by
  simp [coprodMap]

end CoprodMap

end DFinsupp

namespace Submodule

variable [Semiring R] [AddCommMonoid N] [Module R N]

open DFinsupp

section DecidableEq

variable [DecidableEq ι]

/-
**Submodule.dfinsuppSum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dfinsuppSum_mem {β : ι -> Type*} [forall i, Zero (β i)] [forall (i) (x : β
 i), Decidable (x != 0)] (S : Submodule R N) (f : Π₀ i, β i) (g : forall i, β i 
-> N) (h : forall c, f c != 0 -> g c (f c) in S) : f.sum g in S
参数：β i；i；x : β i；x != 0；S : Submodule R N；f : Π₀ i, β i；g : forall i, β i -> N；h
 : forall c, f c != 0 -> g c (f c) in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dfinsuppSum_mem`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : De
cidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i) → D
ecida…
-/
theorem dfinsuppSum_mem {β : ι → Type*} [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    (S : Submodule R N) (f : Π₀ i, β i) (g : ∀ i, β i → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
    f.sum g ∈ S :=
  _root_.dfinsuppSum_mem S f g h
/-
**Submodule.dfinsuppSumAddHom_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dfinsuppSumAddHom_mem {β : ι -> Type*} [forall i, AddZeroClass (β i)] (S :
 Submodule R N) (f : Π₀ i, β i) (g : forall i, β i ->+ N) (h : forall c, f c != 
0 -> g c (f c) in S) : DFinsupp.sumAddHom g f in S
参数：β i；S : Submodule R N；f : Π₀ i, β i；g : forall i, β i ->+ N；h : forall c, f c
 != 0 -> g c (f c) in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dfinsuppSumAddHom_mem`：dfinsuppSumAddHom_mem [forall i, AddZeroClass (β 
i)] [AddCommMonoid γ] {S : Type*} [SetLike S γ] [AddSubmonoidClass S γ] (s : S) 
(f : Π₀ i, …
-/
theorem dfinsuppSumAddHom_mem {β : ι → Type*} [∀ i, AddZeroClass (β i)] (S : Submodule R N)
    (f : Π₀ i, β i) (g : ∀ i, β i →+ N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
    DFinsupp.sumAddHom g f ∈ S :=
  _root_.dfinsuppSumAddHom_mem S f g h

/-- The supremum of a family of submodules is equal to the range of `DFinsupp.lsum`; that is
every element in the `iSup` can be produced from taking a finite number of non-zero elements
of `p i`, coercing them to `N`, and summing them. -/
/-
**Submodule.iSup_eq_range_dfinsupp_lsum** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iSup_eq_range_dfinsupp_lsum (p : ι -> Submodule R N) : iSup p = LinearMap.
range (DFinsupp.lsum Nat fun i => (p i).subtype)
参数：p : ι -> Submodule R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `Submodule.dfinsuppSumAddHom_mem`：dfinsuppSumAddHom_mem {β : ι -> Type*} 
[forall i, AddZeroClass (β i)] (S : Submodule R N) (f : Π₀ i, β i) (g : forall i
, β i ->+ N) (h : for…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The supremum of a family of submodules is equal to the range of `DFinsupp.lsum`;
 that is
every element in the `iSup` can be produced from taking a finite number of non-z
ero elements
of `p i`, coercing them to `N`, and summing them.
-/
theorem iSup_eq_range_dfinsupp_lsum (p : ι → Submodule R N) :
    iSup p = LinearMap.range (DFinsupp.lsum ℕ fun i => (p i).subtype) := by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    simp only [LinearMap.mem_range, lsum_apply_apply]
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsuppSumAddHom_mem _ v _ fun i _ => (le_iSup p i : p i ≤ _) (v i).2

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`DFinsupp.sumAddHom` composed with `DFinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `iSup` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
/-
**Submodule.biSup_eq_range_dfinsupp_lsum** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：biSup_eq_range_dfinsupp_lsum (p : ι -> Prop) [DecidablePred p] (S : ι -> S
ubmodule R N) : ⨆ (i) (_ : p i), S i = LinearMap.range (LinearMap.comp (DFinsupp
.lsum Nat (fun i => (S i).subtype)) (DFinsupp.filterLinearMap R _ p))
参数：p : ι -> Prop；S : ι -> Submodule R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `DFinsupp.filterLinearMap_apply`：∀ {ι : Type u} (γ : Type w) (β : ι → Typ
e v) [inst : Semiring γ] [inst_1 : (i : ι) → AddCommMonoid (β i)]   [inst_2 : (i
 : ι) → _root_.Modul…
· 使用定理 `DFinsupp.filter_single_pos`：filter_single_pos {p : ι -> Prop} [Decidable
Pred p] (i : ι) (x : β i) (h : p i) : (single i x).filter p = single i x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.dfinsuppSumAddHom_mem`：dfinsuppSumAddHom_mem {β : ι -> Type*} 
[forall i, AddZeroClass (β i)] (S : Submodule R N) (f : Π₀ i, β i) (g : forall i
, β i ->+ N) (h : for…
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M

--- 原说明 ---
The bounded supremum of a family of commutative additive submonoids is equal to 
the range of
`DFinsupp.sumAddHom` composed with `DFinsupp.filter_add_monoid_hom`; that is, ev
ery element in the
bounded `iSup` can be produced from taking a finite number of non-zero elements 
from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them.
-/
theorem biSup_eq_range_dfinsupp_lsum (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N) :
    ⨆ (i) (_ : p i), S i =
      LinearMap.range
        (LinearMap.comp
          (DFinsupp.lsum ℕ (fun i => (S i).subtype))
            (DFinsupp.filterLinearMap R _ p)) := by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [LinearMap.comp_apply, filterLinearMap_apply, filter_single_pos _ _ hi]
    simp only [lsum_apply_apply, sumAddHom_single, LinearMap.toAddMonoidHom_coe, coe_subtype]
  · rintro x ⟨v, rfl⟩
    refine dfinsuppSumAddHom_mem _ _ _ fun i _ => ?_
    refine mem_iSup_of_mem i ?_
    by_cases hp : p i
    · simp [hp]
    · simp [hp]

/-- A characterisation of the span of a family of submodules.

See also `Submodule.mem_iSup_iff_exists_finsupp`. -/
/-
**Submodule.mem_iSup_iff_exists_dfinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_iSup_iff_exists_dfinsupp (p : ι -> Submodule R N) (x : N) : x in iSup 
p ↔ exists f : Π₀ i, p i, DFinsupp.lsum Nat (fun i => (p i).subtype) f = x
参数：p : ι -> Submodule R N；x : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Submodule.iSup_eq_range_dfinsupp_lsum`：iSup_eq_range_dfinsupp_lsum (p : 
ι -> Submodule R N) : iSup p = LinearMap.range (DFinsupp.lsum Nat fun i => (p i)
.subtype)

--- 原说明 ---
A characterisation of the span of a family of submodules.

See also `Submodule.mem_iSup_iff_exists_finsupp`.
-/
theorem mem_iSup_iff_exists_dfinsupp (p : ι → Submodule R N) (x : N) :
    x ∈ iSup p ↔
      ∃ f : Π₀ i, p i, DFinsupp.lsum ℕ (fun i => (p i).subtype) f = x :=
  SetLike.ext_iff.mp (iSup_eq_range_dfinsupp_lsum p) x

/-- A variant of `Submodule.mem_iSup_iff_exists_dfinsupp` with the RHS fully unfolded.

See also `Submodule.mem_iSup_iff_exists_finsupp`. -/
/-
**Submodule.mem_iSup_iff_exists_dfinsupp'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_iSup_iff_exists_dfinsupp' (p : ι -> Submodule R N) [forall (i) (x : p 
i), Decidable (x != 0)] (x : N) : x in iSup p ↔ exists f : Π₀ i, p i, (f.sum fun
 _ xi => ↑xi) = x
参数：p : ι -> Submodule R N；i；x : p i；x != 0；x : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_iSup_iff_exists_dfinsupp`：mem_iSup_iff_exists_dfinsupp (p 
: ι -> Submodule R N) (x : N) : x in iSup p ↔ exists f : Π₀ i, p i, DFinsupp.lsu
m Nat (fun i => (p i).subtyp…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A variant of `Submodule.mem_iSup_iff_exists_dfinsupp` with the RHS fully unfolde
d.

See also `Submodule.mem_iSup_iff_exists_finsupp`.
-/
theorem mem_iSup_iff_exists_dfinsupp' (p : ι → Submodule R N) [∀ (i) (x : p i), Decidable (x ≠ 0)]
    (x : N) : x ∈ iSup p ↔ ∃ f : Π₀ i, p i, (f.sum fun _ xi => ↑xi) = x := by
  rw [mem_iSup_iff_exists_dfinsupp]
  simp_rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
    LinearMap.toAddMonoidHom_coe, coe_subtype]
/-
**Submodule.mem_biSup_iff_exists_dfinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_biSup_iff_exists_dfinsupp (p : ι -> Prop) [DecidablePred p] (S : ι -> 
Submodule R N) (x : N) : (x in ⨆ (i) (_ : p i), S i) ↔ exists f : Π₀ i, S i, DFi
nsupp.lsum Nat (fun i => (S i).subtype) (f.filter p) = x
参数：p : ι -> Prop；S : ι -> Submodule R N；x : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Submodule.biSup_eq_range_dfinsupp_lsum`：biSup_eq_range_dfinsupp_lsum (p 
: ι -> Prop) [DecidablePred p] (S : ι -> Submodule R N) : ⨆ (i) (_ : p i), S i =
 LinearMap.range (LinearMap.…
-/
theorem mem_biSup_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p] (S : ι → Submodule R N)
    (x : N) :
    (x ∈ ⨆ (i) (_ : p i), S i) ↔
      ∃ f : Π₀ i, S i,
        DFinsupp.lsum ℕ (fun i => (S i).subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (biSup_eq_range_dfinsupp_lsum p S) x

end DecidableEq

/-
**Submodule.mem_iSup_iff_exists_finsupp** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mem_iSup_iff_exists_finsupp (p : ι -> Submodule R N) (x : N) : x in iSup p
 ↔ exists (f : ι ->₀ N), (forall i, f i in p i) ∧ (f.sum fun _i xi => xi) = x
参数：p : ι -> Submodule R N；x : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_iSup_iff_exists_dfinsupp'`：mem_iSup_iff_exists_dfinsupp' (
p : ι -> Submodule R N) [forall (i) (x : p i), Decidable (x != 0)] (x : N) : x i
n iSup p ↔ exists f : Π₀ i, p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_not`：∀ {p : Prop} {α : Sort u_1} [hn : Decidable ¬p] [h : Decidable
 p] (x : ¬p → α) (y : ¬¬p → α),   dite (¬p) x y = dite p (fun h => y ⋯) x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mem_iSup_iff_exists_finsupp (p : ι → Submodule R N) (x : N) :
    x ∈ iSup p ↔ ∃ (f : ι →₀ N), (∀ i, f i ∈ p i) ∧ (f.sum fun _i xi ↦ xi) = x := by
  classical
  rw [mem_iSup_iff_exists_dfinsupp']
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨⟨f.support, fun i ↦ (f i : N), by simp⟩, by simp, hf⟩, ?_⟩
  rintro ⟨f, hf, rfl⟩
  refine ⟨DFinsupp.mk f.support fun i ↦ ⟨f i, hf i⟩, Finset.sum_congr ?_ fun i hi ↦ ?_⟩
  · ext; simp [mk_eq_zero]
  · simp [Finsupp.mem_support_iff.mp hi]
/-
**Submodule.mem_iSup_finset_iff_exists_sum** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：mem_iSup_finset_iff_exists_sum {s : Finset ι} (p : ι -> Submodule R N) (a 
: N) : (a in ⨆ i in s, p i) ↔ exists μ : forall i, p i, (∑ i in s, (μ i : N)) = 
a
参数：p : ι -> Submodule R N；a : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_iSup_iff_exists_dfinsupp'`：mem_iSup_iff_exists_dfinsupp' (
p : ι -> Submodule R N) [forall (i) (x : p i), Decidable (x != 0)] (x : N) : x i
n iSup p ↔ exists f : Π₀ i, p…
· 使用定理 `iSup_const_le`：iSup_const_le : ⨆ _ : ι, a <= a
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `DFinsupp.mem_support_iff`：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in
 f.support ↔ f i != 0
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Submodule.coe_zero`：coe_zero : ((0 : p) : M) = 0
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `DFinsupp.support_mk_subset`：support_mk_subset {s : Finset ι} {x : forall
 i : (↑s : Set ι), β i.1} : (mk s x).support subseteq s
· 使用定理 `DFinsupp.mk_of_mem`：mk_of_mem (hi : i in s) : (mk s x : forall i, β i) i
 = x ⟨i, hi⟩
-/
theorem mem_iSup_finset_iff_exists_sum {s : Finset ι} (p : ι → Submodule R N) (a : N) :
    (a ∈ ⨆ i ∈ s, p i) ↔ ∃ μ : ∀ i, p i, (∑ i ∈ s, (μ i : N)) = a := by
  classical
    rw [Submodule.mem_iSup_iff_exists_dfinsupp']
    constructor <;> rintro ⟨μ, hμ⟩
    · use fun i => ⟨μ i, (iSup_const_le : _ ≤ p i) (coe_mem <| μ i)⟩
      rw [← hμ]
      symm
      apply Finset.sum_subset
      · intro x
        contrapose
        intro hx
        rw [mem_support_iff, not_ne_iff]
        ext
        rw [coe_zero, ← mem_bot R]
        suffices ⊥ = ⨆ (_ : x ∈ s), p x from this.symm ▸ coe_mem (μ x)
        exact (iSup_neg hx).symm
      · intro x _ hx
        rw [mem_support_iff, not_ne_iff] at hx
        rw [hx]
        rfl
    · refine ⟨DFinsupp.mk s ?_, ?_⟩
      · rintro ⟨i, hi⟩
        refine ⟨μ i, ?_⟩
        rw [iSup_pos]
        · exact coe_mem _
        · exact hi
      simp only [DFinsupp.sum]
      rw [Finset.sum_subset support_mk_subset, ← hμ]
      · exact Finset.sum_congr rfl fun x hx => by rw [mk_of_mem hx]
      · intro x _ hx
        rw [mem_support_iff, not_ne_iff] at hx
        rw [hx]
        rfl

end Submodule

open DFinsupp

section Semiring

variable [DecidableEq ι] [Semiring R] [AddCommMonoid N] [Module R N]

/-- Independence of a family of submodules can be expressed as a quantifier over `DFinsupp`s.

This is an intermediate result used to prove
`iSupIndep_of_dfinsupp_lsum_injective` and
`iSupIndep.dfinsupp_lsum_injective`. -/
/-
**iSupIndep_iff_forall_dfinsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_iff_forall_dfinsupp (p : ι -> Submodule R N) : iSupIndep p ↔ for
all (i) (x : p i) (v : Π₀ i : ι, ↥(p i)), lsum Nat (fun i => (p i).subtype) (era
se i v) = x -> x = 0
参数：p : ι -> Submodule R N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `DFinsupp.filter_ne_eq_erase`：filter_ne_eq_erase (f : Π₀ i, β i) (i : ι) 
: f.filter (· != i) = f.erase i
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.forall'`：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Pr
op}, (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Independence of a family of submodules can be expressed as a quantifier over `DF
insupp`s.

This is an intermediate result used to prove
`iSupIndep_of_dfinsupp_lsum_injective` and
`iSupIndep.dfinsupp_lsum_injective`.
-/
theorem iSupIndep_iff_forall_dfinsupp (p : ι → Submodule R N) :
    iSupIndep p ↔
      ∀ (i) (x : p i) (v : Π₀ i : ι, ↥(p i)),
        lsum ℕ (fun i => (p i).subtype) (erase i v) = x → x = 0 := by
  simp_rw [iSupIndep_def, Submodule.disjoint_def,
    Submodule.mem_biSup_iff_exists_dfinsupp, exists_imp, filter_ne_eq_erase]
  refine forall_congr' fun i => Subtype.forall'.trans ?_
  simp_rw [Submodule.coe_eq_zero]

/-- If `DFinsupp.lsum` applied with `Submodule.subtype` is injective then the submodules are
iSupIndep. -/
/-
**iSupIndep_of_dfinsupp_lsum_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_of_dfinsupp_lsum_injective (p : ι -> Submodule R N) (h : Functio
n.Injective (lsum Nat fun i => (p i).subtype)) : iSupIndep p
参数：p : ι -> Submodule R N；h : Function.Injective (lsum Nat fun i => (p i).subtyp
e)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSupIndep_iff_forall_dfinsupp`：iSupIndep_iff_forall_dfinsupp (p : ι -> S
ubmodule R N) : iSupIndep p ↔ forall (i) (x : p i) (v : Π₀ i : ι, ↥(p i)), lsum 
Nat (fun i => (p i)…
· 使用定理 `DFinsupp.lsum_single`：lsum_single [Semiring S] [Module S N] [SMulCommCla
ss R S N] (F : forall i, M i ->ₗ[R] N) (i) (x : M i) : lsum S F (single i x) = F
 i x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯

--- 原说明 ---
If `DFinsupp.lsum` applied with `Submodule.subtype` is injective then the submod
ules are
iSupIndep.
-/
theorem iSupIndep_of_dfinsupp_lsum_injective (p : ι → Submodule R N)
    (h : Function.Injective (lsum ℕ fun i => (p i).subtype)) :
    iSupIndep p := by
  rw [iSupIndep_iff_forall_dfinsupp]
  intro i x v hv
  replace hv : lsum ℕ (fun i => (p i).subtype) (erase i v) =
      lsum ℕ (fun i => (p i).subtype) (single i x) := by
    simpa only [lsum_single] using! hv
  have := DFunLike.ext_iff.mp (h hv) i
  simpa [eq_comm] using! this

/-- If `DFinsupp.sumAddHom` applied with `AddSubmonoid.subtype` is injective then the additive
submonoids are independent. -/
/-
**iSupIndep_of_dfinsuppSumAddHom_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_of_dfinsuppSumAddHom_injective (p : ι -> AddSubmonoid N) (h : Fu
nction.Injective (sumAddHom fun i => (p i).subtype)) : iSupIndep p
参数：p : ι -> AddSubmonoid N；h : Function.Injective (sumAddHom fun i => (p i).subt
ype)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSupIndep_map_orderIso_iff`：iSupIndep_map_orderIso_iff {ι : Sort*} {α β 
: Type*} [CompleteLattice α] [CompleteLattice β] (f : α ≃o β) {a : ι -> α} : iSu
pIndep (f ∘ a) ↔…
· 使用定理 `iSupIndep_of_dfinsupp_lsum_injective`：iSupIndep_of_dfinsupp_lsum_injecti
ve (p : ι -> Submodule R N) (h : Function.Injective (lsum Nat fun i => (p i).sub
type)) : iSupIndep p

--- 原说明 ---
If `DFinsupp.sumAddHom` applied with `AddSubmonoid.subtype` is injective then th
e additive
submonoids are independent.
-/
theorem iSupIndep_of_dfinsuppSumAddHom_injective (p : ι → AddSubmonoid N)
    (h : Function.Injective (sumAddHom fun i => (p i).subtype)) : iSupIndep p := by
  rw [← iSupIndep_map_orderIso_iff (AddSubmonoid.toNatSubmodule : AddSubmonoid N ≃o _)]
  exact iSupIndep_of_dfinsupp_lsum_injective _ h

/-- Combining `DFinsupp.lsum` with `LinearMap.toSpanSingleton` is the same as
`Finsupp.linearCombination` -/
/-
**lsum_comp_mapRange_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lsum_comp_mapRange_toSpanSingleton [forall m : R, Decidable (m != 0)] (p :
 ι -> Submodule R N) {v : ι -> N} (hv : forall i : ι, v i in p i) : (lsum Nat fu
n i => (p i).subtype : _ ->ₗ[R] _).comp ((mapRange.linearMap fun i => LinearMap.
toSpanSingleton R (↥(p i)) ⟨v i, hv i⟩ : _ ->ₗ[R] _).comp (finsuppLequivDFinsupp
 R : (ι ->₀ R) ≃ₗ[R] _).toLinearMap) = Finsupp.linearCombination R v
参数：m != 0；p : ι -> Submodule R N；hv : forall i : ι, v i in p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finsupp.toDFinsupp_single`：Finsupp.toDFinsupp_single (i : ι) (m : M) : (
Finsupp.single i m).toDFinsupp = DFinsupp.single i m
· 使用定理 `DFinsupp.mapRange.linearMap_apply`：∀ {ι : Type u_1} {R : Type u_3} [inst
 : Semiring R] {β₁ : ι → Type u_8} {β₂ : ι → Type u_9}   [inst_1 : (i : ι) → Add
CommMonoid (β₁ i)] [ins…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `DFinsupp.mapRange.congr_simp`：∀ {ι : Type u} {β₁ : ι → Type v₁} {β₂ : ι 
→ Type v₂} [inst : (i : ι) → Zero (β₁ i)] [inst_1 : (i : ι) → Zero (β₂ i)]   (f 
f_1 : (i : ι) → β₁…
· 使用定理 `DFinsupp.mapRange_single`：mapRange_single {f : forall i, β₁ i -> β₂ i} {
hf : forall i, f i 0 = 0} {i : ι} {b : β₁ i} : mapRange f hf (single i b) = sing
le i (f i b)
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Combining `DFinsupp.lsum` with `LinearMap.toSpanSingleton` is the same as
`Finsupp.linearCombination`
-/
theorem lsum_comp_mapRange_toSpanSingleton [∀ m : R, Decidable (m ≠ 0)] (p : ι → Submodule R N)
    {v : ι → N} (hv : ∀ i : ι, v i ∈ p i) :
    (lsum ℕ fun i => (p i).subtype : _ →ₗ[R] _).comp
        ((mapRange.linearMap fun i => LinearMap.toSpanSingleton R (↥(p i)) ⟨v i, hv i⟩ :
              _ →ₗ[R] _).comp
          (finsuppLequivDFinsupp R : (ι →₀ R) ≃ₗ[R] _).toLinearMap) =
      Finsupp.linearCombination R v := by
  ext
  simp

end Semiring

section Ring

variable [DecidableEq ι] [Ring R] [AddCommGroup N] [Module R N]

/-- If `DFinsupp.sumAddHom` applied with `AddSubmonoid.subtype` is injective then the additive
subgroups are independent. -/
/-
**iSupIndep_of_dfinsuppSumAddHom_injective'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_of_dfinsuppSumAddHom_injective' (p : ι -> AddSubgroup N) (h : Fu
nction.Injective (sumAddHom fun i => (p i).subtype)) : iSupIndep p
参数：p : ι -> AddSubgroup N；h : Function.Injective (sumAddHom fun i => (p i).subty
pe)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSupIndep_map_orderIso_iff`：iSupIndep_map_orderIso_iff {ι : Sort*} {α β 
: Type*} [CompleteLattice α] [CompleteLattice β] (f : α ≃o β) {a : ι -> α} : iSu
pIndep (f ∘ a) ↔…
· 使用定理 `iSupIndep_of_dfinsupp_lsum_injective`：iSupIndep_of_dfinsupp_lsum_injecti
ve (p : ι -> Submodule R N) (h : Function.Injective (lsum Nat fun i => (p i).sub
type)) : iSupIndep p

--- 原说明 ---
If `DFinsupp.sumAddHom` applied with `AddSubmonoid.subtype` is injective then th
e additive
subgroups are independent.
-/
theorem iSupIndep_of_dfinsuppSumAddHom_injective' (p : ι → AddSubgroup N)
    (h : Function.Injective (sumAddHom fun i => (p i).subtype)) : iSupIndep p := by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)]
  exact iSupIndep_of_dfinsupp_lsum_injective _ h

/-- The canonical map out of a direct sum of a family of submodules is injective when the submodules
are `iSupIndep`.

Note that this is not generally true for `[Semiring R]`, for instance when `A` is the
`ℕ`-submodules of the positive and negative integers.

See `Counterexamples/DirectSumIsInternal.lean` for a proof of this fact. -/
/-
**iSupIndep.dfinsupp_lsum_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.dfinsupp_lsum_injective {p : ι -> Submodule R N} (h : iSupIndep 
p) : Function.Injective (lsum Nat fun i => (p i).subtype)
参数：h : iSupIndep p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `DFinsupp.zero_apply`：zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `iSupIndep_iff_forall_dfinsupp`：iSupIndep_iff_forall_dfinsupp (p : ι -> S
ubmodule R N) : iSupIndep p ↔ forall (i) (x : p i) (v : Π₀ i : ι, ↥(p i)), lsum 
Nat (fun i => (p i)…
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `Submodule.coe_neg`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   (x : ↥p), 
↑(-x) =…
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `Submodule.subtype_apply`：subtype_apply (x : p) : p.subtype x = x
· 使用定理 `DFinsupp.lsum_single`：lsum_single [Semiring S] [Module S N] [SMulCommCla
ss R S N] (F : forall i, M i ->ₗ[R] N) (i) (x : M i) : lsum S F (single i x) = F
 i x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `DFinsupp.erase_add_single`：erase_add_single (i : ι) (f : Π₀ i, β i) : f.
erase i + single i (f i) = f
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f

--- 原说明 ---
The canonical map out of a direct sum of a family of submodules is injective whe
n the submodules
are `iSupIndep`.

Note that this is not generally true for `[Semiring R]`, for instance when `A` i
s the
`ℕ`-submodules of the positive and negative integers.

See `Counterexamples/DirectSumIsInternal.lean` for a proof of this fact.
-/
theorem iSupIndep.dfinsupp_lsum_injective {p : ι → Submodule R N} (h : iSupIndep p) :
    Function.Injective (lsum ℕ fun i => (p i).subtype) := by
  -- simplify everything down to binders over equalities in `N`
  rw [iSupIndep_iff_forall_dfinsupp] at h
  suffices LinearMap.ker (lsum ℕ fun i => (p i).subtype) = ⊥ by
    -- Lean can't find this without our help
    let thisI : AddCommGroup (Π₀ i, p i) := inferInstance
    rw [LinearMap.ker_eq_bot] at this
    exact this
  rw [LinearMap.ker_eq_bot']
  intro m hm
  ext i : 1
  -- split `m` into the piece at `i` and the pieces elsewhere, to match `h`
  rw [DFinsupp.zero_apply, ← neg_eq_zero]
  refine h i (-m i) m ?_
  rwa [← erase_add_single i m, map_add, lsum_single, Submodule.subtype_apply,
    add_eq_zero_iff_eq_neg, ← Submodule.coe_neg] at hm

/-- The canonical map out of a direct sum of a family of additive subgroups is injective when the
additive subgroups are `iSupIndep`. -/
/-
**iSupIndep.dfinsuppSumAddHom_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.dfinsuppSumAddHom_injective {p : ι -> AddSubgroup N} (h : iSupIn
dep p) : Function.Injective (sumAddHom fun i => (p i).subtype)
参数：h : iSupIndep p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.dfinsupp_lsum_injective`：iSupIndep.dfinsupp_lsum_injective {p 
: ι -> Submodule R N} (h : iSupIndep p) : Function.Injective (lsum Nat fun i => 
(p i).subtype)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSupIndep_map_orderIso_iff`：iSupIndep_map_orderIso_iff {ι : Sort*} {α β 
: Type*} [CompleteLattice α] [CompleteLattice β] (f : α ≃o β) {a : ι -> α} : iSu
pIndep (f ∘ a) ↔…

--- 原说明 ---
The canonical map out of a direct sum of a family of additive subgroups is injec
tive when the
additive subgroups are `iSupIndep`.
-/
theorem iSupIndep.dfinsuppSumAddHom_injective {p : ι → AddSubgroup N} (h : iSupIndep p) :
    Function.Injective (sumAddHom fun i => (p i).subtype) := by
  rw [← iSupIndep_map_orderIso_iff (AddSubgroup.toIntSubmodule : AddSubgroup N ≃o _)] at h
  exact h.dfinsupp_lsum_injective

/-- A family of submodules over an additive group are independent if and only iff `DFinsupp.lsum`
applied with `Submodule.subtype` is injective.

Note that this is not generally true for `[Semiring R]`; see
`iSupIndep.dfinsupp_lsum_injective` for details. -/
/-
**iSupIndep_iff_dfinsupp_lsum_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_iff_dfinsupp_lsum_injective (p : ι -> Submodule R N) : iSupIndep
 p ↔ Function.Injective (lsum Nat fun i => (p i).subtype)
参数：p : ι -> Submodule R N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.dfinsupp_lsum_injective`：iSupIndep.dfinsupp_lsum_injective {p 
: ι -> Submodule R N} (h : iSupIndep p) : Function.Injective (lsum Nat fun i => 
(p i).subtype)
· 使用定理 `iSupIndep_of_dfinsupp_lsum_injective`：iSupIndep_of_dfinsupp_lsum_injecti
ve (p : ι -> Submodule R N) (h : Function.Injective (lsum Nat fun i => (p i).sub
type)) : iSupIndep p

--- 原说明 ---
A family of submodules over an additive group are independent if and only iff `D
Finsupp.lsum`
applied with `Submodule.subtype` is injective.

Note that this is not generally true for `[Semiring R]`; see
`iSupIndep.dfinsupp_lsum_injective` for details.
-/
theorem iSupIndep_iff_dfinsupp_lsum_injective (p : ι → Submodule R N) :
    iSupIndep p ↔ Function.Injective (lsum ℕ fun i => (p i).subtype) :=
  ⟨iSupIndep.dfinsupp_lsum_injective, iSupIndep_of_dfinsupp_lsum_injective p⟩

omit [DecidableEq ι] in
/-
**iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (p : ι -> Submodule R N) : iSu
pIndep p ↔ forall (s : Finset ι) (v : ι -> N), (forall i in s, v i in p i) -> (∑
 i in s, v i = 0) -> forall i in s, v i = 0
参数：p : ι -> Submodule R N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
· 使用定理 `add_eq_zero_iff_neg_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ -a = b
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `Submodule.sum_mem_biSup`：sum_mem_biSup {ι : Type*} {s : Finset ι} {f : ι
 -> M} {p : ι -> Submodule R M} (h : forall i in s, f i in p i) : (∑ i in s, f i
) in ⨆ i in s…
· 使用引理 `Submodule.mem_iSup_iff_exists_finsupp`：mem_iSup_iff_exists_finsupp (p : 
ι -> Submodule R N) (x : N) : x in iSup p ↔ exists (f : ι ->₀ N), (forall i, f i
 in p i) ∧ (f.sum fun _i xi…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
-/
theorem iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (p : ι → Submodule R N) :
    iSupIndep p ↔ ∀ (s : Finset ι) (v : ι → N),
    (∀ i ∈ s, v i ∈ p i) → (∑ i ∈ s, v i = 0) → ∀ i ∈ s, v i = 0 := by
  classical
  simp_rw [iSupIndep_def, Submodule.disjoint_def]
  constructor
  · intro h s v hv hv0 i hi
    apply h _ _ (hv i hi)
    rw [← s.add_sum_erase _ hi, add_eq_zero_iff_neg_eq] at hv0
    rw [← Submodule.neg_mem_iff, hv0]
    exact SetLike.le_def.mp (biSup_mono <| by grind) (Submodule.sum_mem_biSup <| by grind)
  · intro h i x hx hsup
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp ..).mp hsup
    contrapose! h
    use insert i f.support, fun j ↦ if j = i then -f.sum fun _ x ↦ x else f j
    refine ⟨fun j hj ↦ ?_, ?_, by grind⟩
    · beta_reduce
      split_ifs with h
      · exact (p j).neg_mem (h ▸ hx)
      · simpa [h] using hf j
    · specialize hf i
      simp at hf
      grind [Finsupp.sum, Finset.sum_congr]

@[deprecated (since := "2026-04-08")]
alias iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero := iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero

omit [DecidableEq ι] in
/-
**iSupIndep_iff_finsetSum_eq_imp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_iff_finsetSum_eq_imp_eq (p : ι -> Submodule R N) : iSupIndep p ↔
 forall (s : Finset ι) (v w : ι -> N), (forall i in s, v i in p i ∧ w i in p i) 
-> (∑ i in s, v i = ∑ i in s, w i) -> forall i in s, v i = w i
参数：p : ι -> Submodule R N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`：iSupIndep_iff_finsetSum_eq_
zero_imp_eq_zero (p : ι -> Submodule R N) : iSupIndep p ↔ forall (s : Finset ι) 
(v : ι -> N), (forall i in s, v i…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem iSupIndep_iff_finsetSum_eq_imp_eq (p : ι → Submodule R N) :
    iSupIndep p ↔ ∀ (s : Finset ι) (v w : ι → N),
    (∀ i ∈ s, v i ∈ p i ∧ w i ∈ p i) → (∑ i ∈ s, v i = ∑ i ∈ s, w i) → ∀ i ∈ s, v i = w i := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  constructor
  · intro h s v w hvw
    simpa [sub_eq_zero] using h s (v - w) fun i hi => (p i).sub_mem (hvw i hi).1 (hvw i hi).2
  · intro h s v hv hv0
    specialize h s v 0
    simp_all

@[deprecated (since := "2026-04-08")]
alias iSupIndep_iff_finset_sum_eq_imp_eq := iSupIndep_iff_finsetSum_eq_imp_eq

/-- A family of additive subgroups over an additive group are independent if and only if
`DFinsupp.sumAddHom` applied with `AddSubgroup.subtype` is injective. -/
/-
**iSupIndep_iff_dfinsuppSumAddHom_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_iff_dfinsuppSumAddHom_injective (p : ι -> AddSubgroup N) : iSupI
ndep p ↔ Function.Injective (sumAddHom fun i => (p i).subtype)
参数：p : ι -> AddSubgroup N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.dfinsuppSumAddHom_injective`：iSupIndep.dfinsuppSumAddHom_injec
tive {p : ι -> AddSubgroup N} (h : iSupIndep p) : Function.Injective (sumAddHom 
fun i => (p i).subtype)
· 使用定理 `iSupIndep_of_dfinsuppSumAddHom_injective'`：iSupIndep_of_dfinsuppSumAddHo
m_injective' (p : ι -> AddSubgroup N) (h : Function.Injective (sumAddHom fun i =
> (p i).subtype)) : iSupIndep p

--- 原说明 ---
A family of additive subgroups over an additive group are independent if and onl
y if
`DFinsupp.sumAddHom` applied with `AddSubgroup.subtype` is injective.
-/
theorem iSupIndep_iff_dfinsuppSumAddHom_injective (p : ι → AddSubgroup N) :
    iSupIndep p ↔ Function.Injective (sumAddHom fun i => (p i).subtype) :=
  ⟨iSupIndep.dfinsuppSumAddHom_injective, iSupIndep_of_dfinsuppSumAddHom_injective' p⟩

/-- If `(pᵢ)ᵢ` is a family of independent submodules that generates the whole module `N`, then
`N` is isomorphic to the direct sum of the submodules. -/
/-
**iSupIndep.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `iSupIndep`。
形式化陈述：{ι : Type u_1} →   {R : Type u_3} →     {N : Type u_6} →       [DecidableE
q ι] →         [inst : Ring R] →           [inst_1 : AddCommGroup N] →          
   [inst_2 : _root_.Module R N] →               {p : ι → Submodule R N} → iSupIn
dep p → ⨆ i, p i = ⊤ → (Π₀ (i : ι), ↥(p i)) ≃ₗ[R] N
参数：Π₀ (i : ι), ↥(p i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(pᵢ)ᵢ` is a family of independent submodules that generates the whole module
 `N`, then
`N` is isomorphic to the direct sum of the submodules.
-/
@[simps! apply] noncomputable def iSupIndep.linearEquiv {p : ι → Submodule R N} (ind : iSupIndep p)
    (iSup_top : ⨆ i, p i = ⊤) : (Π₀ i, p i) ≃ₗ[R] N :=
  .ofBijective _ ⟨ind.dfinsupp_lsum_injective, by
    rwa [← LinearMap.range_eq_top, ← Submodule.iSup_eq_range_dfinsupp_lsum]⟩

set_option backward.isDefEq.respectTransparency false in
/-
**iSupIndep.linearEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.linearEquiv_symm_apply {p : ι -> Submodule R N} (ind : iSupIndep
 p) (iSup_top : ⨆ i, p i = ⊤) {i : ι} {x : N} (h : x in p i) : (ind.linearEquiv 
iSup_top).symm x = .single i ⟨x, h⟩
参数：ind : iSupIndep p；iSup_top : ⨆ i, p i = ⊤；h : x in p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSupIndep.linearEquiv_symm_apply {p : ι → Submodule R N} (ind : iSupIndep p)
    (iSup_top : ⨆ i, p i = ⊤) {i : ι} {x : N} (h : x ∈ p i) :
    (ind.linearEquiv iSup_top).symm x = .single i ⟨x, h⟩ := by
  simp [← LinearEquiv.eq_symm_apply, iSupIndep.linearEquiv]

/-- If a family of submodules is independent, then a choice of nonzero vector from each submodule
forms a linearly independent family.

See also `iSupIndep.linearIndependent'`. -/
/-
**iSupIndep.linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.linearIndependent [IsDomain R] [IsTorsionFree R N] {ι : Type*} (
p : ι -> Submodule R N) (hp : iSupIndep p) {v : ι -> N} (hv : forall i, v i in p
 i) (hv' : forall i, v i != 0) : LinearIndependent R v
参数：p : ι -> Submodule R N；hp : iSupIndep p；hv : forall i, v i in p i；hv' : foral
l i, v i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `iSupIndep.dfinsupp_lsum_injective`：iSupIndep.dfinsupp_lsum_injective {p 
: ι -> Submodule R N} (h : iSupIndep p) : Function.Injective (lsum Nat fun i => 
(p i).subtype)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lsum_comp_mapRange_toSpanSingleton`：lsum_comp_mapRange_toSpanSingleton [
forall m : R, Decidable (m != 0)] (p : ι -> Submodule R N) {v : ι -> N} (hv : fo
rall i : ι, v i in p i) …
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
If a family of submodules is independent, then a choice of nonzero vector from e
ach submodule
forms a linearly independent family.

See also `iSupIndep.linearIndependent'`.
-/
theorem iSupIndep.linearIndependent [IsDomain R] [IsTorsionFree R N] {ι : Type*}
    (p : ι → Submodule R N) (hp : iSupIndep p) {v : ι → N} (hv : ∀ i, v i ∈ p i)
    (hv' : ∀ i, v i ≠ 0) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  let a :=
    DFinsupp.mapRange.linearMap (fun i => LinearMap.toSpanSingleton R (p i) ⟨v i, hv i⟩)
      l.toDFinsupp
  have ha : a = 0 := by
    apply hp.dfinsupp_lsum_injective
    rwa [← lsum_comp_mapRange_toSpanSingleton _ hv] at hl
  ext i
  apply smul_left_injective R (hv' i)
  have : l i • v i = a i := rfl
  simp only [coe_zero, Pi.zero_apply, ZeroMemClass.coe_zero, smul_eq_zero, ha] at this
  simpa
/-
**iSupIndep_iff_linearIndependent_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_iff_linearIndependent_of_ne_zero [IsDomain R] [IsTorsionFree R N
] {ι : Type*} {v : ι -> N} (h_ne_zero : forall i, v i != 0) : iSupIndep (R ∙ v ·
) ↔ LinearIndependent R v where mp hv
参数：h_ne_zero : forall i, v i != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.linearIndependent`：iSupIndep.linearIndependent [IsDomain R] [I
sTorsionFree R N] {ι : Type*} (p : ι -> Submodule R N) (hp : iSupIndep p) {v : ι
 -> N} (hv : fora…
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `LinearIndependent.iSupIndep_span_singleton`：LinearIndependent.iSupIndep_
span_singleton (hv : LinearIndependent R v) : iSupIndep fun i => R ∙ v i
-/
theorem iSupIndep_iff_linearIndependent_of_ne_zero [IsDomain R] [IsTorsionFree R N]
    {ι : Type*} {v : ι → N} (h_ne_zero : ∀ i, v i ≠ 0) :
    iSupIndep (R ∙ v ·) ↔ LinearIndependent R v where
  mp hv := hv.linearIndependent _ (fun i => Submodule.mem_span_singleton_self <| v i) h_ne_zero
  mpr hv := hv.iSupIndep_span_singleton

end Ring

namespace LinearMap

section AddCommMonoid

variable {R : Type*} {R₂ : Type*}
variable {M : Type*} {M₂ : Type*}
variable {ι : Type*}
variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable {σ₁₂ : R →+* R₂}
variable [Module R M] [Module R₂ M₂]

open Submodule

section DFinsupp

open DFinsupp

variable {γ : ι → Type*} [DecidableEq ι]

section Sum

variable [∀ i, Zero (γ i)] [∀ (i) (x : γ i), Decidable (x ≠ 0)]

/-
**LinearMap.coe_dfinsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_dfinsuppSum (t : Π₀ i, γ i) (g : forall i, γ i -> M ->ₛₗ[σ₁₂] M₂) : ⇑(
t.sum g) = t.sum fun i d => g i d
参数：t : Π₀ i, γ i；g : forall i, γ i -> M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_dfinsuppSum (t : Π₀ i, γ i) (g : ∀ i, γ i → M →ₛₗ[σ₁₂] M₂) :
    ⇑(t.sum g) = t.sum fun i d => g i d := rfl

@[simp]
/-
**LinearMap.dfinsuppSum_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：dfinsuppSum_apply (t : Π₀ i, γ i) (g : forall i, γ i -> M ->ₛₗ[σ₁₂] M₂) (b
 : M) : (t.sum g) b = t.sum fun i d => g i d b
参数：t : Π₀ i, γ i；g : forall i, γ i -> M ->ₛₗ[σ₁₂] M₂；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
-/
theorem dfinsuppSum_apply (t : Π₀ i, γ i) (g : ∀ i, γ i → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (t.sum g) b = t.sum fun i d => g i d b :=
  sum_apply _ _ _

end Sum

section SumAddHom

variable [∀ i, AddZeroClass (γ i)]

@[simp]
/-
**LinearMap.map_dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_dfinsuppSumAddHom (f : M ->ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : forall i, 
γ i ->+ M} : f (sumAddHom g t) = sumAddHom (fun i => f.toAddMonoidHom.comp (g i)
) t
参数：f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_dfinsuppSumAddHom`：map_dfinsuppSumAddHom [AddCommMonoid
 R] [AddCommMonoid S] [forall i, AddZeroClass (β i)] (h : R ->+ S) (f : Π₀ i, β 
i) (g : forall i, β i ->…
-/
theorem map_dfinsuppSumAddHom (f : M →ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : ∀ i, γ i →+ M} :
    f (sumAddHom g t) = sumAddHom (fun i => f.toAddMonoidHom.comp (g i)) t :=
  f.toAddMonoidHom.map_dfinsuppSumAddHom _ _

end SumAddHom

end DFinsupp

end AddCommMonoid

end LinearMap

namespace LinearEquiv

variable {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} {ι : Type*}

section DFinsupp

open DFinsupp

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}
variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]
variable {γ : ι → Type*} [DecidableEq ι]

@[simp]
/-
**LinearEquiv.map_dfinsuppSumAddHom** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：map_dfinsuppSumAddHom [forall i, AddZeroClass (γ i)] (f : M ≃ₛₗ[τ₁₂] M₂) (
t : Π₀ i, γ i) (g : forall i, γ i ->+ M) : f (sumAddHom g t) = sumAddHom (fun i 
=> f.toAddEquiv.toAddMonoidHom.comp (g i)) t
参数：γ i；f : M ≃ₛₗ[τ₁₂] M₂；t : Π₀ i, γ i；g : forall i, γ i ->+ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_dfinsuppSumAddHom`：map_dfinsuppSumAddHom [AddCommMonoid R] 
[AddCommMonoid S] [forall i, AddZeroClass (β i)] (h : R ≃+ S) (f : Π₀ i, β i) (g
 : forall i, β i ->+…
-/
theorem map_dfinsuppSumAddHom [∀ i, AddZeroClass (γ i)] (f : M ≃ₛₗ[τ₁₂] M₂) (t : Π₀ i, γ i)
    (g : ∀ i, γ i →+ M) :
    f (sumAddHom g t) = sumAddHom (fun i => f.toAddEquiv.toAddMonoidHom.comp (g i)) t :=
  f.toAddEquiv.map_dfinsuppSumAddHom _ _

end DFinsupp

end LinearEquiv

