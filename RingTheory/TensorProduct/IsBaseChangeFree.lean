/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # Base change of a free module

* `IsBaseChange.basis` : the natural basis of the base change of a module with a basis

* `IsBaseChange.free` : a base change of a free module is free.

-/

@[expose] public section

namespace IsBaseChange

variable {R : Type*} [CommSemiring R]
    {S : Type*} [CommSemiring S] [Algebra R S]
    {V : Type*} [AddCommMonoid V] [Module R V]
    {W : Type*} [AddCommMonoid W] [Module R W] [Module S W] [IsScalarTower R S W]
    {ι : Type*}
    {ε : V →ₗ[R] W}

variable (b : Module.Basis ι R V) (ibc : IsBaseChange S ε)

/-- The basis of a module deduced by base change from a free module with a basis. -/
/-
**IsBaseChange.basis** 是 Mathlib 中的一个定义，位于命名空间 `IsBaseChange`。
形式化陈述：basis : Module.Basis ι S W where repr
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis of a module deduced by base change from a free module with a basis.
-/
noncomputable def basis :
    Module.Basis ι S W where
  repr := (ibc.equiv.symm.trans (b.repr.baseChange R S _ _)).trans
      (finsuppPow ι (linearMap R S)).equiv
/-
**IsBaseChange.basis_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：basis_apply (i) : ibc.basis b i = ε (b i)
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem basis_apply (i) : ibc.basis b i = ε (b i) := by
  simp only [basis, LinearEquiv.baseChange, Module.Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  generalize_proofs _ _ _ _ ibcRA
  have : ibcRA.equiv.symm (Finsupp.single i 1) = 1 ⊗ₜ (Finsupp.single i 1) := by
    simp [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul]
  simp [this, IsBaseChange.equiv_tmul]

set_option backward.isDefEq.respectTransparency false in
/-
**IsBaseChange.basis_repr_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：basis_repr_comp_apply (v i) : (ibc.basis b).repr (ε v) i = algebraMap R S 
(b.repr v i)
参数：v i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `IsBaseChange.basis_apply`：basis_apply (i) : ibc.basis b i = ε (b i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
（共 36 条，此处仅展示前 30 条）
-/
theorem basis_repr_comp_apply (v i) :
    (ibc.basis b).repr (ε v) i = algebraMap R S (b.repr v i) := by
  conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply,
    map_finsuppSum, map_finsuppSum]
  simp only [map_smul, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single i]
  · rw [← IsScalarTower.algebraMap_smul S (b.repr v i) (ε (b i)),
      map_smul, ← ibc.basis_apply]
    simp [Finsupp.single_eq_same, Algebra.algebraMap_eq_smul_one]
  · intro i' _ h
    rw [← IsScalarTower.algebraMap_smul S (b.repr v i') (ε (b i')), map_smul,
      ← ibc.basis_apply]
    simp [Finsupp.single_eq_of_ne (Ne.symm h)]
  · simp
/-
**IsBaseChange.basis_repr_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：basis_repr_comp (v : V) : (ibc.basis b).repr (ε v) = Finsupp.mapRange.line
arMap (Algebra.linearMap R S) (b.repr v)
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBaseChange.basis_repr_comp_apply`：basis_repr_comp_apply (v i) : (ibc.b
asis b).repr (ε v) i = algebraMap R S (b.repr v i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basis_repr_comp (v : V) :
    (ibc.basis b).repr (ε v) =
      Finsupp.mapRange.linearMap (Algebra.linearMap R S) (b.repr v) := by
  ext i
  simp [basis_repr_comp_apply]

include ibc in
/-
**IsBaseChange.free** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：free [Module.Free R V] : Module.Free S W
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
-/
theorem free [Module.Free R V] : Module.Free S W :=
  Module.Free.of_basis (ibc.basis (Module.Free.chooseBasis R V))

end IsBaseChange

section underring

namespace IsBaseChange

open TensorProduct

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  (A : Type*) [CommSemiring A] [Algebra A R]
  [Module A V] [IsScalarTower A R V]

open TensorProduct

variable {ι : Type*} (b : Module.Basis ι R V)

/-
**IsBaseChange.of_basis** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：of_basis : IsBaseChange R (Finsupp.linearCombination A b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用引理 `TensorProduct.finsuppScalarRight_apply_tmul_apply`：finsuppScalarRight_ap
ply_tmul_apply (m : M) (p : ι ->₀ R) (i : ι) : finsuppScalarRight R S M ι (m oti
mesₜ[R] p) i = p i • m
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Finsupp.sum_mapRange_index`：∀ {α : Type u_1} {M : Type u_8} {M' : Type u
_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommMonoid
 N] {f : M → M'}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
theorem of_basis : IsBaseChange R (Finsupp.linearCombination A b) := by
  classical
  let j := TensorProduct.finsuppScalarRight A R R ι
  refine of_equiv ?_ ?_
  · apply LinearEquiv.ofBijective (Finsupp.linearCombination R b ∘ₗ j)
    rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, j.bijective.of_comp_iff]
    simp [Function.Bijective,
        ← span_range_eq_top_iff_surjective_finsuppLinearCombination,
        ← linearIndependent_iff_injective_finsuppLinearCombination,
        Module.Basis.span_eq, b.linearIndependent]
  · intro x
    suffices (j (1 ⊗ₜ[A] x)) = x.mapRange (algebraMap A R) (by simp) by
      simp [this, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
    ext i
    simp [j, Algebra.algebraMap_eq_smul_one]

include A in
/-- Any finite basis of a module can express it as the base change
of a finite free module from any under-ring. -/
/-
**IsBaseChange.of_fintype_basis** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：of_fintype_basis [Fintype ι] : IsBaseChange R (Fintype.linearCombination A
 b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用引理 `TensorProduct.piScalarRight_apply`：piScalarRight_apply (x : N otimes[R] 
(ι -> R)) : piScalarRight R S N ι x = piScalarRightHom R S N ι x
· 使用引理 `TensorProduct.piScalarRightHom_tmul`：piScalarRightHom_tmul (x : N) (f : 
ι -> R) : piScalarRightHom R S N ι (x otimesₜ f) = (fun j => f j • x)
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
Any finite basis of a module can express it as the base change
of a finite free module from any under-ring.
-/
theorem of_fintype_basis [Fintype ι] :
    IsBaseChange R (Fintype.linearCombination A b) := by
  have : DecidableEq ι := Classical.typeDecidableEq ι
  let j : R ⊗[A] (ι → A) ≃ₗ[R] ι → R := piScalarRight A R R ι
  refine of_equiv ?_ ?_
  · apply LinearEquiv.ofBijective (Fintype.linearCombination R b ∘ₗ j)
    rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, j.bijective.of_comp_iff]
    simp [Function.Bijective,
        ← span_range_eq_top_iff_surjective_fintypeLinearCombination,
        ← linearIndependent_iff_injective_fintypeLinearCombination,
        Module.Basis.span_eq, b.linearIndependent]
  · intro x
    -- simp? [Fintype.linearCombination_apply] says:
    simp only [LinearEquiv.ofBijective_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, Fintype.linearCombination_apply]
    congr
    ext i
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    simp

variable {A b} in
/-
**IsBaseChange.of_fintype_basis_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：of_fintype_basis_eq [Fintype ι] {a : ι -> A} {v : V} : (Fintype.linearComb
ination A b) a = v ↔ algebraMap A R ∘ a = b.equivFun v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `Fintype.linearCombination_apply`：Fintype.linearCombination_apply (f) : F
intype.linearCombination R v f = ∑ i, f i • v i
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem of_fintype_basis_eq [Fintype ι] {a : ι → A} {v : V} :
    (Fintype.linearCombination A b) a = v ↔
      algebraMap A R ∘ a = b.equivFun v := by
  rw [← LinearEquiv.symm_apply_eq]
  rw [Fintype.linearCombination_apply, b.equivFun_symm_apply]
  simp

end IsBaseChange

end underring

