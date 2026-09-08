/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The standard basis

This file defines the standard basis `Pi.basis (s : ∀ j, Basis (ι j) R (M j))`,
which is the `Σ j, ι j`-indexed basis of `Π j, M j`. The basis vectors are given by
`Pi.basis s ⟨j, i⟩ j' = Pi.single j' (s j) i = if j = j' then s i else 0`.

The standard basis on `R^η`, i.e. `η → R` is called `Pi.basisFun`.

To give a concrete example, `Pi.single (i : Fin 3) (1 : R)`
gives the `i`th unit basis vector in `R³`, and `Pi.basisFun R (Fin 3)` proves
this is a basis over `Fin 3 → R`.

## Main definitions

- `Pi.basis s`: given a basis `s i` for each `M i`, the standard basis on `Π i, M i`
- `Pi.basisFun R η`: the standard basis on `R^η`, i.e. `η → R`, given by
  `Pi.basisFun R η i j = Pi.single i 1 j = if i = j then 1 else 0`.
- `Matrix.stdBasis R n m`: the standard basis on `Matrix n m R`, given by
  `Matrix.stdBasis R n m (i, j) i' j' = if (i, j) = (i', j') then 1 else 0`.

-/

@[expose] public section

open Function LinearMap Module Set Submodule

namespace Pi
variable {ι R M : Type*}

section Module

variable {η : Type*} {ιs : η → Type*} {Ms : η → Type*}

/-
**Pi.linearIndependent_single** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：linearIndependent_single [Semiring R] [forall i, AddCommMonoid (Ms i)] [fo
rall i, Module R (Ms i)] [DecidableEq η] (v : forall j, ιs j -> Ms j) (hs : fora
ll i, LinearIndependent R (v i)) : LinearIndependent R fun ji : Σ j, ιs j => Pi.
single ji.1 (v ji.1 ji.2)
参数：Ms i；Ms i；v : forall j, ιs j -> Ms j；hs : forall i, LinearIndependent R (v i)
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIndependent.map_injOn`：LinearIndependent.map_injOn (hv : LinearInd
ependent R v) (f : M ->ₗ[R] M') (hf_inj : Set.InjOn f (span R (Set.range v))) : 
LinearIndependent…
· 使用定理 `DFinsupp.linearIndependent_single`：linearIndependent_single (hf : forall
 i, LinearIndependent R (f i)) : LinearIndependent R fun ix : Σ i, φ i => single
 ix.1 (f ix.1 ix.2)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `DFinsupp.injective_pi_lapply`：injective_pi_lapply : Function.Injective (
LinearMap.pi (R
-/
theorem linearIndependent_single [Semiring R] [∀ i, AddCommMonoid (Ms i)] [∀ i, Module R (Ms i)]
    [DecidableEq η] (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent R (v i)) :
    LinearIndependent R fun ji : Σ j, ιs j ↦ Pi.single ji.1 (v ji.1 ji.2) := by
  convert! (DFinsupp.linearIndependent_single _ hs).map_injOn _ DFinsupp.injective_pi_lapply.injOn
/-
**Pi.linearIndependent_single_one** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：linearIndependent_single_one (ι R : Type*) [Semiring R] [DecidableEq ι] : 
LinearIndependent R (fun i : ι => Pi.single i (1 : R))
参数：ι R : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `Pi.linearIndependent_single`：linearIndependent_single [Semiring R] [fora
ll i, AddCommMonoid (Ms i)] [forall i, Module R (Ms i)] [DecidableEq η] (v : for
all j, ιs j -> Ms…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem linearIndependent_single_one (ι R : Type*) [Semiring R] [DecidableEq ι] :
    LinearIndependent R (fun i : ι ↦ Pi.single i (1 : R)) := by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
  exact Pi.linearIndependent_single (fun (_ : ι) (_ : Unit) ↦ (1 : R))
    <| by simp +contextual [Fintype.linearIndependent_iffₛ]
/-
**Pi.linearIndependent_single_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：linearIndependent_single_of_ne_zero [Ring R] [IsDomain R] [AddCommGroup M]
 [Module R M] [IsTorsionFree R M] [DecidableEq ι] {v : ι -> M} (hv : forall i, v
 i != 0) : LinearIndependent R fun i : ι => Pi.single i (v i)
参数：hv : forall i, v i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `Pi.linearIndependent_single`：linearIndependent_single [Semiring R] [fora
ll i, AddCommMonoid (Ms i)] [forall i, Module R (Ms i)] [DecidableEq η] (v : for
all j, ιs j -> Ms…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma linearIndependent_single_of_ne_zero [Ring R] [IsDomain R] [AddCommGroup M] [Module R M]
    [IsTorsionFree R M] [DecidableEq ι] {v : ι → M} (hv : ∀ i, v i ≠ 0) :
    LinearIndependent R fun i : ι ↦ Pi.single i (v i) := by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
  exact linearIndependent_single (fun i (_ : Unit) ↦ v i) <| by simp +contextual [hv]

variable [Semiring R] [∀ i, AddCommMonoid (Ms i)] [∀ i, Module R (Ms i)]

section Fintype

variable [Fintype η]

open LinearEquiv

/-- `Pi.basis (s : ∀ j, Basis (ιs j) R (Ms j))` is the `Σ j, ιs j`-indexed basis on `Π j, Ms j`
given by `s j` on each component.

For the standard basis over `R` on the finite-dimensional space `η → R` see `Pi.basisFun`.
-/
/-
**Pi.basis** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：{R : Type u_2} →   {η : Type u_4} →     {ιs : η → Type u_5} →       {Ms : 
η → Type u_6} →         [inst : Semiring R] →           [inst_1 : (i : η) → AddC
ommMonoid (Ms i)] →             [inst_2 : (i : η) → _root_.Module R (Ms i)] →   
            [Fintype η] → ((j : η) → Module.Basis (ιs j) R (Ms j)) → Module.Basi
s ((j : η) × ιs j) R ((j : η) → Ms j)
参数：i : η；Ms i；i : η；Ms i；(j : η) → Module.Basis (ιs j) R (Ms j)；(j : η) × ιs j；(
j : η) → Ms j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Pi.basis (s : ∀ j, Basis (ιs j) R (Ms j))` is the `Σ j, ιs j`-indexed basis on 
`Π j, Ms j`
given by `s j` on each component.

For the standard basis over `R` on the finite-dimensional space `η → R` see `Pi.
basisFun`.
-/
protected noncomputable def basis (s : ∀ j, Basis (ιs j) R (Ms j)) :
    Basis (Σ j, ιs j) R (∀ j, Ms j) :=
  Basis.ofRepr
    ((LinearEquiv.piCongrRight fun j => (s j).repr) ≪≫ₗ
      (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Pi.basis_repr_single** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：basis_repr_single [DecidableEq η] (s : forall j, Basis (ιs j) R (Ms j)) (j
 i) : (Pi.basis s).repr (Pi.single j (s j i)) = Finsupp.single ⟨j, i⟩ 1
参数：s : forall j, Basis (ιs j) R (Ms j)；j i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
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
· 使用定理 `Finsupp.zero_apply`：zero_apply {a : α} : (0 : α ->₀ M) a = 0
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem basis_repr_single [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (j i) :
    (Pi.basis s).repr (Pi.single j (s j i)) = Finsupp.single ⟨j, i⟩ 1 := by
  classical
  ext ⟨j', i'⟩
  by_cases hj : j = j'
  · subst hj
    simp only [Pi.basis, LinearEquiv.trans_apply,
      LinearEquiv.piCongrRight, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
      Basis.repr_symm_apply, LinearEquiv.coe_mk]
    symm
    simp [Finsupp.single_apply]
  simp only [Pi.basis, LinearEquiv.trans_apply, Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply,
    LinearEquiv.piCongrRight]
  dsimp
  rw [Pi.single_eq_of_ne (Ne.symm hj), map_zero, Finsupp.zero_apply,
    Finsupp.single_eq_of_ne]
  rintro ⟨⟩
  contradiction

@[simp]
/-
**Pi.basis_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：basis_apply [DecidableEq η] (s : forall j, Basis (ιs j) R (Ms j)) (ji) : P
i.basis s ji = Pi.single ji.1 (s ji.1 ji.2)
参数：s : forall j, Basis (ιs j) R (Ms j)；ji。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.basis_repr_single`：basis_repr_single [DecidableEq η] (s : forall j, B
asis (ιs j) R (Ms j)) (j i) : (Pi.basis s).repr (Pi.single j (s j i)) = Finsupp.
single ⟨j,…
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basis_apply [DecidableEq η] (s : ∀ j, Basis (ιs j) R (Ms j)) (ji) :
    Pi.basis s ji = Pi.single ji.1 (s ji.1 ji.2) :=
  Basis.apply_eq_iff.mpr (by simp)

@[simp]
/-
**Pi.basis_repr** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：basis_repr (s : forall j, Basis (ιs j) R (Ms j)) (x) (ji) : (Pi.basis s).r
epr x ji = (s ji.1).repr (x ji.1) ji.2
参数：s : forall j, Basis (ιs j) R (Ms j)；x；ji。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem basis_repr (s : ∀ j, Basis (ιs j) R (Ms j)) (x) (ji) :
    (Pi.basis s).repr x ji = (s ji.1).repr (x ji.1) ji.2 :=
  rfl

end Fintype

section

variable [Finite η]
variable (R η)

/-- The basis on `η → R` where the `i`th basis vector is `Function.update 0 i 1`. -/
/-
**Pi.basisFun** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：basisFun : Basis η R (η -> R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis on `η → R` where the `i`th basis vector is `Function.update 0 i 1`.
-/
noncomputable def basisFun : Basis η R (η → R) :=
  Basis.ofEquivFun (LinearEquiv.refl _ _)

@[simp]
/-
**Pi.basisFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：basisFun_apply [DecidableEq η] (i) : basisFun R η i = Pi.single i 1
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_ofEquivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u
_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] [inst_3 : Finit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisFun_apply [DecidableEq η] (i) :
    basisFun R η i = Pi.single i 1 := by
  simp only [basisFun, Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

@[simp]
/-
**Pi.basisFun_repr** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：basisFun_repr (x : η -> R) (i : η) : (Pi.basisFun R η).repr x i = x i
参数：x : η -> R；i : η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisFun_repr (x : η → R) (i : η) : (Pi.basisFun R η).repr x i = x i := by simp [basisFun]

@[simp]
/-
**Pi.basisFun_equivFun** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：basisFun_equivFun : (Pi.basisFun R η).equivFun = LinearEquiv.refl _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.equivFun_ofEquivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finit…
-/
theorem basisFun_equivFun : (Pi.basisFun R η).equivFun = LinearEquiv.refl _ _ :=
  Basis.equivFun_ofEquivFun _

variable {η}

/-- The `R`-submodule of `η → R` consisting of functions supported in the subset `s`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Pi.spanSubset** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：spanSubset (s : Set η) : Submodule R (η -> R)
参数：s : Set η。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def spanSubset (s : Set η) : Submodule R (η → R) :=
  .span R (Pi.basisFun R η '' s)

variable {R} {s : Set η}
/-
**Pi.mem_spanSubset_iff** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mem_spanSubset_iff {s : Set η} {v : η -> R} : v in spanSubset R s ↔ forall
 i ∉ s, v i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Pi.basisFun_repr`：basisFun_repr (x : η -> R) (i : η) : (Pi.basisFun R η)
.repr x i = x i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_spanSubset_iff {s : Set η} {v : η → R} :
    v ∈ spanSubset R s ↔ ∀ i ∉ s, v i = 0 := by
  simp [spanSubset, Module.Basis.mem_span_image, Finsupp.support_subset_iff]

end

end Module

end Pi

/-- Let `k` be an integral domain and `G` an arbitrary finite set.
Then any algebra morphism `φ : (G → k) →ₐ[k] k` is an evaluation map. -/
/-
**AlgHom.eq_piEvalAlgHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.eq_piEvalAlgHom {k G : Type*} [CommSemiring k] [NoZeroDivisors k] [
Nontrivial k] [Finite G] (φ : (G -> k) ->ₐ[k] k) : exists (s : G), φ = Pi.evalAl
gHom _ _ s
参数：φ : (G -> k) ->ₐ[k] k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_sum_single`：∀ {I : Type u_7} [inst : DecidableEq I] {M : I →
 Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [inst_2 : Fintype I]   (f : 
(i : I) → M …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AlgHomClass.linearMapClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_
3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semi
ring B] [inst_3 …
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Let `k` be an integral domain and `G` an arbitrary finite set.
Then any algebra morphism `φ : (G → k) →ₐ[k] k` is an evaluation map.
-/
lemma AlgHom.eq_piEvalAlgHom {k G : Type*} [CommSemiring k] [NoZeroDivisors k] [Nontrivial k]
    [Finite G] (φ : (G → k) →ₐ[k] k) : ∃ (s : G), φ = Pi.evalAlgHom _ _ s := by
  have h1 := map_one φ
  classical
  have := Fintype.ofFinite G
  simp only [← Finset.univ_sum_single (1 : G → k), Pi.one_apply, map_sum] at h1
  obtain ⟨s, hs⟩ : ∃ (s : G), φ (Pi.single s 1) ≠ 0 := by
    by_contra
    simp_all
  have h2 : ∀ t ≠ s, φ (Pi.single t 1) = 0 := by
    refine fun _ _ ↦ (eq_zero_or_eq_zero_of_mul_eq_zero ?_).resolve_left hs
    rw [← map_mul]
    convert! map_zero φ
    ext u
    by_cases u = s <;> simp_all
  have h3 : φ (Pi.single s 1) = 1 := by
    rwa [Fintype.sum_eq_single s h2] at h1
  use s
  refine AlgHom.toLinearMap_injective ((Pi.basisFun k G).ext fun t ↦ ?_)
  by_cases t = s <;> simp_all

namespace Module

variable (ι R M N : Type*) [Finite ι] [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- The natural linear equivalence: `Mⁱ ≃ Hom(Rⁱ, M)` for an `R`-module `M`. -/
/-
**Module.piEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：piEquiv : (ι -> M) ≃ₗ[R] ((ι -> R) ->ₗ[R] M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural linear equivalence: `Mⁱ ≃ Hom(Rⁱ, M)` for an `R`-module `M`.
-/
noncomputable def piEquiv : (ι → M) ≃ₗ[R] ((ι → R) →ₗ[R] M) := Basis.constr (Pi.basisFun R ι) R
/-
**Module.piEquiv_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：piEquiv_apply_apply (ι R M : Type*) [Fintype ι] [CommSemiring R] [AddCommM
onoid M] [Module R M] (v : ι -> M) (w : ι -> R) : piEquiv ι R M v w = ∑ i, w i •
 v i
参数：ι R M : Type*；v : ι -> M；w : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.constr_apply_fintype`：constr_apply_fintype [Fintype ι] (b :
 Basis ι R M) (f : ι -> M') (x : M) : (constr (M'
-/
lemma piEquiv_apply_apply (ι R M : Type*) [Fintype ι] [CommSemiring R]
    [AddCommMonoid M] [Module R M] (v : ι → M) (w : ι → R) :
    piEquiv ι R M v w = ∑ i, w i • v i := by
  simp only [piEquiv, Basis.constr_apply_fintype, Basis.equivFun_apply]
  congr
/-
**Module.range_piEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [inst : Finite ι] [inst_1 :
 CommSemiring R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] (v : 
ι → M), ((Module.piEquiv ι R M) v).range = Submodule.span R (Set.range v)
参数：ι : Type u_1；R : Type u_2；M : Type u_3；v : ι → M；(Module.piEquiv ι R M) v；Set
.range v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.constr_range`：constr_range {f : ι -> M'} : LinearMap.range 
(constr (M'
-/
@[simp] lemma range_piEquiv (v : ι → M) :
    LinearMap.range (piEquiv ι R M v) = span R (range v) :=
  Basis.constr_range _ _
/-
**Module.surjective_piEquiv_apply_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [inst : Finite ι] [inst_1 :
 CommSemiring R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] (v : 
ι → M),   Function.Surjective ⇑((Module.piEquiv ι R M) v) ↔ Submodule.span R (Se
t.range v) = ⊤
参数：ι : Type u_1；R : Type u_2；M : Type u_3；v : ι → M；(Module.piEquiv ι R M) v；Set
.range v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Module.range_piEquiv`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Finite ι] [inst_1 : CommSemiring R] [inst_2 : AddCommMonoid M]   [inst_3 : 
_root_.Mod…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma surjective_piEquiv_apply_iff (v : ι → M) :
    Surjective (piEquiv ι R M v) ↔ span R (range v) = ⊤ := by
  rw [← LinearMap.range_eq_top, range_piEquiv]

end Module

namespace Module.Free

variable {ι : Type*} (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- The product of finitely many free modules is free. -/
/-
**Module.Free._root_.Module.Free.pi** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of finitely many free modules is free.
-/
instance _root_.Module.Free.pi (M : ι → Type*) [Finite ι] [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] : Module.Free R (∀ i, M i) :=
  let ⟨_⟩ := nonempty_fintype ι
  .of_basis <| Pi.basis fun i => Module.Free.chooseBasis R (M i)

variable (ι) in
/-- The product of finitely many free modules is free (non-dependent version to help with typeclass
search). -/
/-
**Module.Free._root_.Module.Free.function** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of finitely many free modules is free (non-dependent version to help
 with typeclass
search).
-/
instance _root_.Module.Free.function [Finite ι] [Module.Free R M] : Module.Free R (ι → M) :=
  Free.pi _ _

end Module.Free

