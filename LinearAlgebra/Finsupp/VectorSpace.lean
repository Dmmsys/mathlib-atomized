/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.LinearAlgebra.Projection

/-!
# Linear structures on function with finite support `ι →₀ M`

This file contains results on the `R`-module structure on functions of finite support from a type
`ι` to an `R`-module `M`, in particular in the case that `R` is a field.

-/

@[expose] public section


noncomputable section

open Set LinearMap Module Submodule

universe u v w

namespace DFinsupp

variable {ι : Type*} {R : Type*} {M : ι → Type*}
variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The direct sum of free modules is free.

Note that while this is stated for `DFinsupp` not `DirectSum`, the types are defeq. -/
/-
**DFinsupp.basis** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：basis {η : ι -> Type*} (b : forall i, Basis (η i) R (M i)) : Basis (Σ i, η
 i) R (Π₀ i, M i)
参数：b : forall i, Basis (η i) R (M i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct sum of free modules is free.

Note that while this is stated for `DFinsupp` not `DirectSum`, the types are def
eq.
-/
noncomputable def basis {η : ι → Type*} (b : ∀ i, Basis (η i) R (M i)) :
    Basis (Σ i, η i) R (Π₀ i, M i) :=
  .ofRepr
    ((mapRange.linearEquiv fun i => (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm)

variable (R M) in
/-
**DFinsupp._root_.Module.Free.dfinsupp** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Module.Free.dfinsupp [∀ i : ι, Module.Free R (M i)] : Module.Free R (Π₀ i, M i) :=
  .of_basis <| DFinsupp.basis fun i => Module.Free.chooseBasis R (M i)

variable [DecidableEq ι] {φ : ι → Type*} (f : ∀ i, φ i → M i)

open Finsupp (linearCombination)
/-
**DFinsupp.linearIndependent_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：linearIndependent_single (hf : forall i, LinearIndependent R (f i)) : Line
arIndependent R fun ix : Σ i, φ i => single ix.1 (f ix.1 ix.2)
参数：hf : forall i, LinearIndependent R (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `sigmaFinsuppLequivDFinsupp_apply`：∀ {ι : Type u_1} (R : Type u_2) {η : ι
 → Type u_4} {N : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid N]   [in
st_2 : _root_.Module R…
· 使用定理 `sigmaFinsuppAddEquivDFinsupp_apply`：∀ {ι : Type u_1} {η : ι → Type u_4} 
{N : Type u_5} [inst : AddZeroClass N] (a : (i : ι) × η i →₀ N),   sigmaFinsuppA
ddEquivDFinsupp a = sigm…
· 使用定理 `sigmaFinsuppEquivDFinsupp_single`：sigmaFinsuppEquivDFinsupp_single [Deci
dableEq ι] [Zero N] (a : Σ i, η i) (n : N) : sigmaFinsuppEquivDFinsupp (Finsupp.
single a n) = @DFinsup…
· 使用定理 `DFinsupp.mapRange.linearMap_apply`：∀ {ι : Type u_1} {R : Type u_3} [inst
 : Semiring R] {β₁ : ι → Type u_8} {β₂ : ι → Type u_9}   [inst_1 : (i : ι) → Add
CommMonoid (β₁ i)] [ins…
· 使用定理 `DFinsupp.mapRange_single`：mapRange_single {f : forall i, β₁ i -> β₂ i} {
hf : forall i, f i 0 = 0} {i : ι} {b : β₁ i} : mapRange f hf (single i b) = sing
le i (f i b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFinsupp.mapRange_injective`：mapRange_injective (f : forall i, β₁ i -> β
₂ i) (hf : forall i, f i 0 = 0) : Function.Injective (mapRange f hf) ↔ forall i,
 Function.Injecti…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem linearIndependent_single (hf : ∀ i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2) := by
  have : linearCombination R (fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2)) =
    DFinsupp.mapRange.linearMap (fun i ↦ linearCombination R (f i)) ∘ₗ
    (sigmaFinsuppLequivDFinsupp R).toLinearMap := by ext; simp
  rw [LinearIndependent, this]
  exact ((DFinsupp.mapRange_injective _ fun _ ↦ map_zero _).mpr hf).comp (Equiv.injective _)
/-
**DFinsupp.linearIndependent_single_iff** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：linearIndependent_single_iff : LinearIndependent R (fun ix : Σ i, φ i => s
ingle ix.1 (f ix.1 ix.2)) ↔ forall i, LinearIndependent R (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `DFinsupp.linearIndependent_single`：linearIndependent_single (hf : forall
 i, LinearIndependent R (f i)) : LinearIndependent R fun ix : Σ i, φ i => single
 ix.1 (f ix.1 ix.2)
-/
lemma linearIndependent_single_iff :
    LinearIndependent R (fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2)) ↔
      ∀ i, LinearIndependent R (f i) :=
  ⟨fun h i ↦ (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

end DFinsupp

namespace Finsupp

section Semiring

variable {R : Type*} {M : Type*} {ι : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M]

/-
**Finsupp.linearIndependent_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearIndependent_single {φ : ι -> Type*} (f : forall i, φ i -> M) (hf : f
orall i, LinearIndependent R (f i)) : LinearIndependent R fun ix : Σ i, φ i => s
ingle ix.1 (f ix.1 ix.2)
参数：f : forall i, φ i -> M；hf : forall i, LinearIndependent R (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.toFinsupp_single`：DFinsupp.toFinsupp_single (i : ι) (m : M) : (
DFinsupp.single i m : Π₀ _ : ι, M).toFinsupp = Finsupp.single i m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.map_injOn`：LinearIndependent.map_injOn (hv : LinearInd
ependent R v) (f : M ->ₗ[R] M') (hf_inj : Set.InjOn f (span R (Set.range v))) : 
LinearIndependent…
· 使用定理 `DFinsupp.linearIndependent_single`：linearIndependent_single (hf : forall
 i, LinearIndependent R (f i)) : LinearIndependent R fun ix : Σ i, φ i => single
 ix.1 (f ix.1 ix.2)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem linearIndependent_single {φ : ι → Type*} (f : ∀ i, φ i → M)
    (hf : ∀ i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2) := by
  classical
  convert!
    (DFinsupp.linearIndependent_single _ hf).map_injOn _
      (finsuppLequivDFinsupp R).symm.injective.injOn
  simp
/-
**Finsupp.linearIndependent_single_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：linearIndependent_single_iff {φ : ι -> Type*} {f : forall i, φ i -> M} : L
inearIndependent R (fun ix : Σ i, φ i => single ix.1 (f ix.1 ix.2)) ↔ forall i, 
LinearIndependent R (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `Finsupp.linearIndependent_single`：linearIndependent_single {φ : ι -> Typ
e*} (f : forall i, φ i -> M) (hf : forall i, LinearIndependent R (f i)) : Linear
Independent R fun ix :…
-/
lemma linearIndependent_single_iff {φ : ι → Type*} {f : ∀ i, φ i → M} :
    LinearIndependent R (fun ix : Σ i, φ i ↦ single ix.1 (f ix.1 ix.2)) ↔
      ∀ i, LinearIndependent R (f i) :=
  ⟨fun h i ↦ (h.comp _ sigma_mk_injective).of_comp (lsingle i), linearIndependent_single _⟩

open LinearMap Submodule

open scoped Classical in
/-- The basis on `ι →₀ M` with basis vectors `fun ⟨i, x⟩ ↦ single i (b i x)`. -/
/-
**Finsupp.basis** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {ι : Type u_3} →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             {φ : ι → Type u_4} → ((i : ι) → Module.Basis (φ i) R M) → M
odule.Basis ((i : ι) × φ i) R (ι →₀ M)
参数：(i : ι) → Module.Basis (φ i) R M；(i : ι) × φ i；ι →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis on `ι →₀ M` with basis vectors `fun ⟨i, x⟩ ↦ single i (b i x)`.
-/
protected def basis {φ : ι → Type*} (b : ∀ i, Basis (φ i) R M) : Basis (Σ i, φ i) R (ι →₀ M) :=
  .ofRepr <| (finsuppLequivDFinsupp R).trans <|
    (DFinsupp.mapRange.linearEquiv fun i ↦ (b i).repr).trans (sigmaFinsuppLequivDFinsupp R).symm

@[simp]
/-
**Finsupp.basis_repr** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：basis_repr {φ : ι -> Type*} (b : forall i, Basis (φ i) R M) (g : ι ->₀ M) 
(ix) : (Finsupp.basis b).repr g ix = (b ix.1).repr (g ix.1) ix.2
参数：b : forall i, Basis (φ i) R M；g : ι ->₀ M；ix。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem basis_repr {φ : ι → Type*} (b : ∀ i, Basis (φ i) R M) (g : ι →₀ M) (ix) :
    (Finsupp.basis b).repr g ix = (b ix.1).repr (g ix.1) ix.2 :=
  rfl

@[simp]
/-
**Finsupp.coe_basis** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_basis {φ : ι -> Type*} (b : forall i, Basis (φ i) R M) : ⇑(Finsupp.bas
is b) = fun ix : Σ i, φ i => single ix.1 (b ix.1 ix.2)
参数：b : forall i, Basis (φ i) R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply_left`：single_apply_left {f : α -> β} (hf : Function
.Injective f) (x z : α) (y : M) : single (f x) y (f z) = single x y z
· 使用定理 `sigma_mk_injective`：∀ {α : Type u_1} {β : α → Type u_4} {i : α}, Functio
n.Injective (Sigma.mk i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
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
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem coe_basis {φ : ι → Type*} (b : ∀ i, Basis (φ i) R M) :
    ⇑(Finsupp.basis b) = fun ix : Σ i, φ i => single ix.1 (b ix.1 ix.2) :=
  funext fun ⟨i, x⟩ =>
    Basis.apply_eq_iff.mpr <| by
      ext ⟨j, y⟩
      by_cases h : i = j
      · cases h
        simp [Finsupp.single_apply_left sigma_mk_injective]
      · simp_all

variable (ι R M) in
/-
**Finsupp._root_.Module.Free.finsupp** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Module.Free.finsupp [Module.Free R M] : Module.Free R (ι →₀ M) :=
  .of_basis (Finsupp.basis fun _ => Module.Free.chooseBasis R M)

/-- The basis on `ι →₀ R` with basis vectors `fun i ↦ single i 1`. -/
@[simps]
/-
**Finsupp.basisSingleOne** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{R : Type u_1} → {ι : Type u_3} → [inst : Semiring R] → Module.Basis ι R (
ι →₀ R)
参数：ι →₀ R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis on `ι →₀ R` with basis vectors `fun i ↦ single i 1`.
-/
protected def basisSingleOne : Basis ι R (ι →₀ R) :=
  Basis.ofRepr (LinearEquiv.refl _ _)

@[simp]
/-
**Finsupp.coe_basisSingleOne** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_basisSingleOne : (Finsupp.basisSingleOne : ι -> ι ->₀ R) = fun i => Fi
nsupp.single i 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
-/
theorem coe_basisSingleOne : (Finsupp.basisSingleOne : ι → ι →₀ R) = fun i => Finsupp.single i 1 :=
  funext fun _ => Basis.apply_eq_iff.mpr rfl

variable (ι R) in
/-
**Finsupp.linearIndependent_single_one** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：linearIndependent_single_one : LinearIndependent R fun i : ι => single i (
1 : R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
-/
lemma linearIndependent_single_one : LinearIndependent R fun i : ι ↦ single i (1 : R) :=
  Finsupp.basisSingleOne.linearIndependent
/-
**Finsupp.isCompl_range_lmapDomain_span** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：isCompl_range_lmapDomain_span {α β : Type*} {u : α -> ι} {v : β -> ι} (huv
 : IsCompl (Set.range u) (Set.range v)) : IsCompl (LinearMap.range (lmapDomain R
 R u)) (.span R (.range fun x => single (v x) 1))
参数：huv : IsCompl (Set.range u) (Set.range v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.range_lmapDomain`：range_lmapDomain {β : Type*} (u : α -> β) : Li
nearMap.range (lmapDomain R R u) = .span R (.range fun x => single (u x) 1)
· 使用引理 `LinearIndependent.isCompl_span_image`：LinearIndependent.isCompl_span_ima
ge (h₁ : LinearIndependent R v) (h₂ : Submodule.span R (Set.range v) = ⊤) {s t :
 Set ι} (hst : IsCompl s t…
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
lemma isCompl_range_lmapDomain_span {α β : Type*}
    {u : α → ι} {v : β → ι} (huv : IsCompl (Set.range u) (Set.range v)) :
    IsCompl (LinearMap.range (lmapDomain R R u)) (.span R (.range fun x ↦ single (v x) 1)) := by
  rw [range_lmapDomain]
  have := (Finsupp.basisSingleOne (R := R)).linearIndependent.isCompl_span_image
     (Module.Basis.span_eq _) huv
  rwa [← Set.range_comp, ← Set.range_comp, Function.comp_def] at this

end Semiring

section Ring
variable {R M ι : Type*} [Ring R] [AddCommGroup M]

/-
**Finsupp.linearIndependent_single_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp
`。
形式化陈述：linearIndependent_single_of_ne_zero [IsDomain R] [Module R M] [IsTorsionFr
ee R M] {v : ι -> M} (hv : forall i, v i != 0) : LinearIndependent R fun i : ι =
> single i (v i)
参数：hv : forall i, v i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `Finsupp.linearIndependent_single`：linearIndependent_single {φ : ι -> Typ
e*} (f : forall i, φ i -> M) (hf : forall i, LinearIndependent R (f i)) : Linear
Independent R fun ix :…
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
lemma linearIndependent_single_of_ne_zero [IsDomain R] [Module R M] [IsTorsionFree R M] {v : ι → M}
    (hv : ∀ i, v i ≠ 0) : LinearIndependent R fun i : ι ↦ single i (v i) := by
  rw [← linearIndependent_equiv (Equiv.sigmaPUnit ι)]
  exact linearIndependent_single (f := fun i (_ : Unit) ↦ v i) <| by simp +contextual [hv]

set_option backward.isDefEq.respectTransparency false in
/-
**Finsupp.lcomapDomain_eq_linearProjOfIsCompl** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp
`。
形式化陈述：lcomapDomain_eq_linearProjOfIsCompl {α β : Type*} {u : α -> ι} {v : β -> ι
} (hu : u.Injective) (h : IsCompl (Set.range u) (Set.range v)) : lcomapDomain u 
hu = LinearMap.linearProjOfIsCompl (.span R (Set.range fun x : β => single (v x)
 (1 : R))) (lmapDomain _ _ u) (mapDomain_injective hu) (isCompl_range_lmapDomain
_span h)
参数：hu : u.Injective；h : IsCompl (Set.range u) (Set.range v)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Finsupp.mapDomain_injective`：mapDomain_injective {f : α -> β} (hf : Func
tion.Injective f) : Function.Injective (mapDomain f : (α ->₀ M) -> β ->₀ M)
· 使用引理 `Finsupp.isCompl_range_lmapDomain_span`：isCompl_range_lmapDomain_span {α 
β : Type*} {u : α -> ι} {v : β -> ι} (huv : IsCompl (Set.range u) (Set.range v))
 : IsCompl (LinearMap.range…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_basisSingleOne`：coe_basisSingleOne : (Finsupp.basisSingleOne
 : ι -> ι ->₀ R) = fun i => Finsupp.single i 1
· 使用定理 `Finsupp.lcomapDomain_apply`：∀ {α : Type u_1} {M : Type u_2} {R : Type u_
5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 {β : Type u_9} …
· 使用定理 `Finsupp.comapDomain_single`：comapDomain_single (f : α -> β) (a : α) (m :
 M) (hif : Set.InjOn f (f ⁻¹' (single (f a) m).support)) : comapDomain f (Finsup
p.single (f a) m…
· 使用定理 `LinearMap.linearProjOfIsCompl_apply_left`：linearProjOfIsCompl_apply_left
 (x : F) : linearProjOfIsCompl q i hi h (i x) = x
· 使用引理 `LinearMap.linearProjOfIsCompl_apply_right'`：linearProjOfIsCompl_apply_ri
ght' (x : E) (hx : x in q) : linearProjOfIsCompl q i hi h x = 0
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Set.disjoint_range_iff`：disjoint_range_iff {β γ : Sort*} {x : β -> α} {y
 : γ -> α} : Disjoint (range x) (range y) ↔ forall i j, x i != y j
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma lcomapDomain_eq_linearProjOfIsCompl {α β : Type*}
    {u : α → ι} {v : β → ι} (hu : u.Injective) (h : IsCompl (Set.range u) (Set.range v)) :
    lcomapDomain u hu =
      LinearMap.linearProjOfIsCompl (.span R (Set.range fun x : β ↦ single (v x) (1 : R)))
        (lmapDomain _ _ u) (mapDomain_injective hu) (isCompl_range_lmapDomain_span h) := by
  classical
  refine Finsupp.basisSingleOne.ext fun i ↦ ?_
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ : i ∈ Set.range u ⊔ .range v := by rw [codisjoint_iff.mp h.2]; trivial
  · have : single (u i) 1 = lmapDomain R R u (.single i 1) := by simp
    simp only [coe_basisSingleOne, lcomapDomain_apply, comapDomain_single]
    rw [this, LinearMap.linearProjOfIsCompl_apply_left]
  · rw [LinearMap.linearProjOfIsCompl_apply_right']
    · ext j
      simp only [coe_basisSingleOne, lcomapDomain_apply, comapDomain_apply, single_apply,
        coe_zero, Pi.zero_apply, ite_eq_right_iff]
      intro hij
      exact (Set.disjoint_range_iff.mp h.1 j i hij.symm).elim
    · exact Submodule.subset_span ⟨i, rfl⟩

end Ring

end Finsupp

/-
**Module.Free.trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.Free.trans {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R
 S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Fr
ee S M] [Module.Free R S] : Module.Free R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.finsupp_cod`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
-/
lemma Module.Free.trans {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Free S M]
    [Module.Free R S] : Module.Free R M :=
  let e : (ChooseBasisIndex S M →₀ S) ≃ₗ[R] ChooseBasisIndex S M →₀ (ChooseBasisIndex R S →₀ R) :=
    Finsupp.mapRange.linearEquiv (chooseBasis R S).repr
  let e : M ≃ₗ[R] ChooseBasisIndex S M →₀ (ChooseBasisIndex R S →₀ R) :=
    (chooseBasis S M).repr.restrictScalars R ≪≫ₗ e
  .of_equiv e.symm

/-! TODO: move this section to an earlier file. -/


namespace Basis

variable {R M n : Type*}
variable [DecidableEq n]
variable [Semiring R] [AddCommMonoid M] [Module R M]

/-
**Basis._root_.Finset.sum_single_ite** 是 Mathlib 中的一个定理，位于命名空间 `Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.sum_single_ite [Fintype n] (a : R) (i : n) :
    (∑ x : n, Finsupp.single x (if i = x then a else 0)) = Finsupp.single i a := by
  simp only [apply_ite (Finsupp.single _), Finsupp.single_zero, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

@[simp]
/-
**Basis.equivFun_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Basis`。
形式化陈述：equivFun_symm_single [Finite n] (b : Basis n R M) (i : n) : b.equivFun.sym
m (Pi.single i 1) = b i
参数：b : Basis n R M；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivFun_symm_single [Finite n] (b : Basis n R M) (i : n) :
    b.equivFun.symm (Pi.single i 1) = b i := by
  cases nonempty_fintype n
  simp [Pi.single_apply]

end Basis

section Algebra

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] {ι : Type*} (B : Basis ι R S)

/-- For any `r : R`, `s : S`, we have
  `B.repr ((algebra_map R S r) * s) i = r * (B.repr s i) `. -/
/-
**Module.Basis.repr_smul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.repr_smul' (i : ι) (r : R) (s : S) : B.repr (algebraMap R S r
 * s) i = r * B.repr s i
参数：i : ι；r : R；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.smul_apply`：smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v :
 α ->₀ M) (a : α) : (b • v) a = b • v a

--- 原说明 ---
For any `r : R`, `s : S`, we have
  `B.repr ((algebra_map R S r) * s) i = r * (B.repr s i) `.
-/
theorem Module.Basis.repr_smul' (i : ι) (r : R) (s : S) :
    B.repr (algebraMap R S r * s) i = r * B.repr s i := by
  rw [← smul_eq_mul, ← smul_eq_mul, algebraMap_smul, map_smul, Finsupp.smul_apply]

end Algebra

namespace FreeAbelianGroup

/-
**FreeAbelianGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FreeAbelianGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ : Type*} : Module.Free ℤ (FreeAbelianGroup σ) where
  exists_basis := ⟨σ, ⟨(FreeAbelianGroup.equivFinsupp _).toIntLinearEquiv⟩⟩

end FreeAbelianGroup

namespace AddMonoidAlgebra
variable {M R S : Type*} [Semiring R] [Semiring S] [Module R S] [Module.Free R S]

/-
**AddMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `AddMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free R S[M] := .of_equiv (coeffLinearEquiv _).symm

end AddMonoidAlgebra

namespace MonoidAlgebra
variable {M R S : Type*} [Semiring R] [Semiring S] [Module R S] [Module.Free R S]

/-
**MonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free R S[M] := .of_equiv (coeffLinearEquiv _).symm

end MonoidAlgebra

namespace Polynomial
variable {R S : Type*} [Semiring R] [Semiring S] [Module R S] [Module.Free R S]

/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free R R[X] := .of_equiv (Polynomial.toFinsuppIsoLinear _).symm

end Polynomial

