/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.ErdosKaplansky
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.
This file contains basic results on dual vector spaces.

## Main definitions

* Submodules:
  * `Submodule.dualRestrict_comap W'` is the dual annihilator of `W' : Submodule R (Dual R M)`,
    pulled back along `Module.Dual.eval R M`.
  * `Submodule.dualCopairing W` is the canonical pairing between `W.dualAnnihilator` and `M ⧸ W`.
    It is nondegenerate for vector spaces (`subspace.dualCopairing_nondegenerate`).
* Vector spaces:
  * `Subspace.dualLift W` is an arbitrary section (using choice) of `Submodule.dualRestrict W`.

## Main results

* Annihilators:
  * `LinearMap.ker_dual_map_eq_dualAnnihilator_range` says that
    `f.dual_map.ker = f.range.dualAnnihilator`
  * `LinearMap.range_dual_map_eq_dualAnnihilator_ker_of_subtype_range_surjective` says that
    `f.dual_map.range = f.ker.dualAnnihilator`; this is specialized to vector spaces in
    `LinearMap.range_dual_map_eq_dualAnnihilator_ker`.
  * `Submodule.dualQuotEquivDualAnnihilator` is the equivalence
    `Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator`
  * `Submodule.quotDualCoannihilatorToDual` is the nondegenerate pairing
    `M ⧸ W.dualCoannihilator →ₗ[R] Dual R W`.
    It is a perfect pairing when `R` is a field and `W` is finite-dimensional.
* Vector spaces:
  * `Subspace.dualAnnihilator_dualCoannihilator_eq` says that the double dual annihilator,
    pulled back ground `Module.Dual.eval`, is the original submodule.
  * `Subspace.dualAnnihilator_gci` says that `module.dualAnnihilator_gc R M` is an
    antitone Galois coinsertion.
  * `Subspace.quotAnnihilatorEquiv` is the equivalence
    `Dual K V ⧸ W.dualAnnihilator ≃ₗ[K] Dual K W`.
  * `LinearMap.id_nondegenerate` says that `LinearMap.id` is nondegenerate as a bilinear pairing.
  * `LinearMap.eval_nondegenerate` says that `Dual.eval` is nondegenerate.
  * `Subspace.is_compl_dualAnnihilator` says that the dual annihilator carries complementary
    subspaces to complementary subspaces.
* Finite-dimensional vector spaces:
  * `Subspace.orderIsoFiniteCodimDim` is the antitone order isomorphism between
    finite-codimensional subspaces of `V` and finite-dimensional subspaces of `Dual K V`.
  * `Subspace.orderIsoFiniteDimensional` is the antitone order isomorphism between
    subspaces of a finite-dimensional vector space `V` and subspaces of its dual.
  * `Subspace.quotDualEquivAnnihilator W` is the equivalence
    `(Dual K V ⧸ W.dualLift.range) ≃ₗ[K] W.dualAnnihilator`, where `W.dualLift.range` is a copy
    of `Dual K W` inside `Dual K V`.
  * `Subspace.quotEquivAnnihilator W` is the equivalence `(V ⧸ W) ≃ₗ[K] W.dualAnnihilator`
  * `Subspace.dualQuotDistrib W` is an equivalence
    `Dual K (V₁ ⧸ W) ≃ₗ[K] Dual K V₁ ⧸ W.dualLift.range` from an arbitrary choice of
    splitting of `V₁`.
-/

@[expose] public section

open Module Submodule

noncomputable section

namespace Module

variable (R A M : Type*)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

section Prod

variable (M' : Type*) [AddCommMonoid M'] [Module R M']

/-- Taking duals distributes over products. -/
@[simps!]
/-
**Module.dualProdDualEquivDual** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：dualProdDualEquivDual : (Module.Dual R M × Module.Dual R M') ≃ₗ[R] Module.
Dual R (M × M')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking duals distributes over products.
-/
def dualProdDualEquivDual : (Module.Dual R M × Module.Dual R M') ≃ₗ[R] Module.Dual R (M × M') :=
  LinearMap.coprodEquiv R

@[simp]
/-
**Module.dualProdDualEquivDual_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：dualProdDualEquivDual_apply (φ : Module.Dual R M) (ψ : Module.Dual R M') :
 dualProdDualEquivDual R M M' (φ, ψ) = φ.coprod ψ
参数：φ : Module.Dual R M；ψ : Module.Dual R M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualProdDualEquivDual_apply (φ : Module.Dual R M) (ψ : Module.Dual R M') :
    dualProdDualEquivDual R M M' (φ, ψ) = φ.coprod ψ :=
  rfl

end Prod

end Module

section

open Module Module.Dual Submodule LinearMap Cardinal Function

universe uR uM uK uV uι
variable {R : Type uR} {M : Type uM} {K : Type uK} {V : Type uV} {ι : Type uι}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

section Finite

variable [Finite ι]

-- Not sure whether this is true for free modules over a commutative ring
/-- A vector space over a field is isomorphic to its dual if and only if it is finite-dimensional:
  a consequence of the Erdős-Kaplansky theorem. -/
/-
**Basis.linearEquiv_dual_iff_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Basis.linearEquiv_dual_iff_finiteDimensional [Field K] [AddCommGroup V] [M
odule K V] : Nonempty (V ≃ₗ[K] Dual K V) ↔ FiniteDimensional K V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteDimensional.eq_1`：∀ (K : Type u_1) (V : Type u_2) [inst : Division
Ring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   FiniteDimensio
nal K V = Mo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.rank_lt_aleph0_iff`：rank_lt_aleph0_iff : Module.rank R M < ℵ₀ ↔ M
odule.Finite R M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `lift_rank_lt_rank_dual`：lift_rank_lt_rank_dual {K : Type u} {V : Type v}
 [Field K] [AddCommGroup V] [Module K V] (h : ℵ₀ <= Module.rank K V) : Cardinal.
lift.{u} (Mo…
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
A vector space over a field is isomorphic to its dual if and only if it is finit
e-dimensional:
  a consequence of the Erdős-Kaplansky theorem.
-/
theorem Basis.linearEquiv_dual_iff_finiteDimensional [Field K] [AddCommGroup V] [Module K V] :
    Nonempty (V ≃ₗ[K] Dual K V) ↔ FiniteDimensional K V := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ ⟨(Module.Free.chooseBasis K V).toDualEquiv⟩⟩
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  by_contra!
  apply (lift_rank_lt_rank_dual this).ne
  have := e.lift_rank_eq
  rwa [lift_umax, lift_id'.{uV}] at this
/-
**Module.Basis.dual_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.dual_rank_eq (b : Basis ι R M) : Module.rank R (Dual R M) = C
ardinal.lift.{uR, uM} (Module.rank R M)
参数：b : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
-/
theorem Module.Basis.dual_rank_eq (b : Basis ι R M) :
    Module.rank R (Dual R M) = Cardinal.lift.{uR, uM} (Module.rank R M) := by
  classical rw [← lift_umax.{uM, uR}, b.toDualEquiv.lift_rank_eq, lift_id'.{uM, uR}]

end Finite

namespace Module

variable [Module.Finite R M]

/-
**Module.dual_free** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
形式化陈述：dual_free [Free R M] : Free R (Dual R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance dual_free [Free R M] : Free R (Dual R M) :=
  Free.of_basis (Free.chooseBasis R M).dualBasis
/-
**Module.dual_projective** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
形式化陈述：dual_projective [Projective R M] : Projective R (Dual R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Finite.exists_comp_eq_id_of_projective`：exists_comp_eq_id_of_proj
ective [Module.Finite R M] [Projective R M] : exists (n : Nat) (f : (Fin n -> R)
 ->ₗ[R] M) (g : M ->ₗ[R] Fin n -> R…
· 使用定理 `Module.Projective.of_split`：∀ {R : Type u_1} [inst : Semiring R] {P : Ty
pe u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3}
 [inst_3 : AddCo…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance dual_projective [Projective R M] : Projective R (Dual R M) :=
  have ⟨_, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  .of_split f.dualMap g.dualMap (congr_arg dualMap hfg)
/-
**Module.dual_finite** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
形式化陈述：dual_finite [Projective R M] : Module.Finite R (Dual R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Finite.exists_comp_eq_id_of_projective`：exists_comp_eq_id_of_proj
ective [Module.Finite R M] [Projective R M] : exists (n : Nat) (f : (Fin n -> R)
 ->ₗ[R] M) (g : M ->ₗ[R] Fin n -> R…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `LinearMap.surjective_of_comp_eq_id`：surjective_of_comp_eq_id : Surjectiv
e g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance dual_finite [Projective R M] : Module.Finite R (Dual R M) :=
  have ⟨n, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  have := Finite.of_basis (Free.chooseBasis R <| Fin n → R).dualBasis
  .of_surjective _ (surjective_of_comp_eq_id f.dualMap g.dualMap <| congr_arg dualMap hfg)

end Module

end CommSemiring

end

namespace Module

universe uK uV
variable {K : Type uK} {V : Type uV}
variable [CommSemiring K] [AddCommMonoid V] [Module K V] [Projective K V]

open Module Module.Dual Submodule LinearMap Cardinal Module

section

variable (K)

/-
**Module.eval_apply_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：eval_apply_injective : Function.Injective (eval K V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.projective_def'`：projective_def' : Projective R P ↔ exists s : P 
->ₗ[R] P ->₀ R, Finsupp.linearCombination R id ∘ₗ s = .id
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Module.Basis.eval_injective`：eval_injective {ι : Type*} (b : Basis ι R M
) : Function.Injective (Dual.eval R M)
· 使用定理 `LinearMap.injective_of_comp_eq_id`：injective_of_comp_eq_id : Injective f
-/
theorem eval_apply_injective : Function.Injective (eval K V) :=
  have ⟨s, hs⟩ := Module.projective_def'.mp ‹Projective K V›
  .of_comp (f := s.dualMap.dualMap)
    (Finsupp.basisSingleOne.eval_injective.comp <| injective_of_comp_eq_id s _ hs)

variable (V)
/-
**Module.eval_ker** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：eval_ker : LinearMap.ker (eval K V) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.eval_apply_injective`：eval_apply_injective : Function.Injective (
eval K V)
-/
theorem eval_ker : LinearMap.ker (eval K V) = ⊥ := ker_eq_bot_of_injective (eval_apply_injective K)
/-
**Module.map_eval_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：map_eval_injective : (Submodule.map (eval K V)).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.eval_apply_injective`：eval_apply_injective : Function.Injective (
eval K V)
-/
theorem map_eval_injective : (Submodule.map (eval K V)).Injective :=
  Submodule.map_injective_of_injective (eval_apply_injective K)
/-
**Module.comap_eval_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：comap_eval_surjective : (Submodule.comap (eval K V)).Surjective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_surjective_of_injective`：comap_surjective_of_injective :
 Function.Surjective (comap f)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.eval_apply_injective`：eval_apply_injective : Function.Injective (
eval K V)
-/
theorem comap_eval_surjective : (Submodule.comap (eval K V)).Surjective :=
  Submodule.comap_surjective_of_injective (eval_apply_injective K)

end

section

variable (K)

/-
**Module.eval_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：eval_apply_eq_zero_iff (v : V) : (eval K V) v = 0 ↔ v = 0
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Module.eval_ker`：eval_ker : LinearMap.ker (eval K V) = ⊥
-/
theorem eval_apply_eq_zero_iff (v : V) : (eval K V) v = 0 ↔ v = 0 :=
  SetLike.ext_iff.mp (eval_ker K V) v

/-- This is a linear map version of `SeparatingDual.exists_ne_zero` in a projective module. -/
/-
**Module.Projective.exists_dual_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projec
tive`。
形式化陈述：∀ {V : Type uV} [inst : AddCommMonoid V] (R : Type u_1) [inst_1 : Semiring
 R] [inst_2 : _root_.Module R V]   [Module.Projective R V] {x : V}, x ≠ 0 → ∃ f,
 f x ≠ 0
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Projective.iff_split`：∀ {R : Type u} [inst : Semiring R] {P : Typ
e v} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P],   Module.Projectiv
e R P ↔ ∃ M x x_1…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `LinearMap.map_eq_zero_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8
} {M₃ : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddComm
Monoid M] [inst…
· 使用定理 `LinearMap.injective_of_comp_eq_id`：injective_of_comp_eq_id : Injective f
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `LinearEquiv.map_ne_zero_iff`：map_ne_zero_iff {x : M} : e x != 0 ↔ x != 0
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g

--- 原说明 ---
This is a linear map version of `SeparatingDual.exists_ne_zero` in a projective 
module.
-/
theorem Projective.exists_dual_ne_zero (R : Type*) [Semiring R] [Module R V]
    [Projective R V] {x : V} (hx : x ≠ 0) : ∃ f : Dual R V, f x ≠ 0 :=
  have ⟨M, _, _, _, ⟨i, s, his⟩⟩ := Projective.iff_split.mp ‹Projective R V›
  let b := Free.chooseBasis R M
  have : i x ≠ 0 := i.map_eq_zero_iff (injective_of_comp_eq_id i s his) |>.not.mpr hx
  have ⟨j, hj⟩ := not_forall.mp fun h ↦ b.repr.map_ne_zero_iff.mpr this <| Finsupp.ext h
  ⟨b.coord j ∘ₗ i, hj⟩
/-
**Module.forall_dual_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：forall_dual_apply_eq_zero_iff (R : Type*) [Semiring R] [Module R V] [Proje
ctive R V] (v : V) : (forall φ : Module.Dual R V, φ v = 0) ↔ v = 0
参数：R : Type*；v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Module.Projective.exists_dual_ne_zero`：∀ {V : Type uV} [inst : AddCommMo
noid V] (R : Type u_1) [inst_1 : Semiring R] [inst_2 : _root_.Module R V]   [Mod
ule.Projective R V] {x : V}…
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
theorem forall_dual_apply_eq_zero_iff
    (R : Type*) [Semiring R] [Module R V] [Projective R V] (v : V) :
    (∀ φ : Module.Dual R V, φ v = 0) ↔ v = 0 := by
  refine ⟨fun h ↦ ?_, fun hv ↦ by simp [hv]⟩
  contrapose! h
  exact Projective.exists_dual_ne_zero R h

/-- This is a linear map version of `SeparatingDual.exists_eq_one` in a projective module. -/
/-
**Module.Projective.exists_dual_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Module.Project
ive`。
形式化陈述：∀ {V : Type uV} [inst : AddCommMonoid V] (K : Type u_1) [inst_1 : Semifiel
d K] [inst_2 : _root_.Module K V]   [Module.Projective K V] {x : V}, x ≠ 0 → ∃ f
, f x = 1
参数：K : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.exists_dual_ne_zero`：∀ {V : Type uV} [inst : AddCommMo
noid V] (R : Type u_1) [inst_1 : Semiring R] [inst_2 : _root_.Module R V]   [Mod
ule.Projective R V] {x : V}…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1

--- 原说明 ---
This is a linear map version of `SeparatingDual.exists_eq_one` in a projective m
odule.
-/
theorem Projective.exists_dual_eq_one (K : Type*) [Semifield K] [Module K V] [Projective K V]
    {x : V} (hx : x ≠ 0) : ∃ f : Dual K V, f x = 1 :=
  have ⟨f, hf⟩ := exists_dual_ne_zero K hx
  ⟨(f x)⁻¹ • f, inv_mul_cancel₀ hf⟩

@[simp]
/-
**Module.subsingleton_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：subsingleton_dual_iff : Subsingleton (Dual K V) ↔ Subsingleton V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.eval_apply_injective`：eval_apply_injective : Function.Injective (
eval K V)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem subsingleton_dual_iff : Subsingleton (Dual K V) ↔ Subsingleton V :=
  ⟨fun _ ↦ ⟨fun _ _ ↦ eval_apply_injective K (Subsingleton.elim ..)⟩, fun _ ↦ inferInstance⟩

@[simp]
/-
**Module.nontrivial_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：nontrivial_dual_iff : Nontrivial (Dual K V) ↔ Nontrivial V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.subsingleton_dual_iff`：subsingleton_dual_iff : Subsingleton (Dual
 K V) ↔ Subsingleton V
-/
theorem nontrivial_dual_iff : Nontrivial (Dual K V) ↔ Nontrivial V := by
  contrapose!; exact subsingleton_dual_iff K
/-
**Module.instNontrivialDual** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
形式化陈述：instNontrivialDual [Nontrivial V] : Nontrivial (Dual K V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.nontrivial_dual_iff`：nontrivial_dual_iff : Nontrivial (Dual K V) 
↔ Nontrivial V
-/
instance instNontrivialDual [Nontrivial V] : Nontrivial (Dual K V) :=
  (nontrivial_dual_iff K).mpr inferInstance

omit [Projective K V] in
/-- For an example of a non-free projective `K`-module `V` for which the forward implication
fails, see https://stacks.math.columbia.edu/tag/05WG#comment-9913. -/
/-
**Module.finite_dual_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finite_dual_iff [Free K V] : Module.Finite K (Dual K V) ↔ Module.Finite K 
V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_subsingleton`：∀ (R : Type u_1) (M : Type u_2) [Subsingle
ton R] [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M], IsNoetherian…
· 使用定理 `Module.Finite.exists_nat_not_surjective`：Module.Finite.exists_nat_not_su
rjective [RankCondition R] (M) [AddCommMonoid M] [Module R M] [Module.Finite R M
] : exists n : Nat, forall f …
· 使用定理 `rankCondition_of_nontrivial_of_commSemiring`：∀ {R : Type u_4} [inst : Co
mmSemiring R] [Nontrivial R], RankCondition R
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Function.Injective.surjective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β} [Nonempty γ],   Function.Injective f → Function.Sur
jective fun g => g ∘ f
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…

--- 原说明 ---
For an example of a non-free projective `K`-module `V` for which the forward imp
lication
fails, see https://stacks.math.columbia.edu/tag/05WG#comment-9913.
-/
theorem finite_dual_iff [Free K V] : Module.Finite K (Dual K V) ↔ Module.Finite K V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  have ⟨⟨ι, b⟩⟩ := Free.exists_basis (R := K) (M := V)
  cases finite_or_infinite ι
  · exact .of_basis b
  nontriviality K
  have ⟨n, hn⟩ := Module.Finite.exists_nat_not_surjective K (Dual K V)
  let g := Finsupp.llift K K K ι ≪≫ₗ b.repr.dualMap
  exact hn (LinearMap.funLeft K K (Fin.valEmbedding.trans (Infinite.natEmbedding ι)) ∘ₗ _)
    ((Function.Embedding.injective _).surjective_comp_right.comp g.symm.surjective) |>.elim

end

omit [Projective K V]

/-
**Module.dual_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：dual_rank_eq [Free K V] [Module.Finite K V] : Module.rank K (Dual K V) = C
ardinal.lift.{uK, uV} (Module.rank K V)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.dual_rank_eq`：Module.Basis.dual_rank_eq (b : Basis ι R M) :
 Module.rank R (Dual R M) = Cardinal.lift.{uR, uM} (Module.rank R M)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem dual_rank_eq [Free K V] [Module.Finite K V] :
    Module.rank K (Dual K V) = Cardinal.lift.{uK, uV} (Module.rank K V) :=
  (Free.chooseBasis K V).dual_rank_eq

section IsReflexive

open Function

variable (R M N : Type*)
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- See also `Module.instFiniteDimensionalOfIsReflexive` for the converse over a field. -/
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `Module.instFiniteDimensionalOfIsReflexive` for the converse over a fie
ld.
-/
instance (priority := 900) IsReflexive.of_finite_of_free [Module.Finite R M] [Free R M] :
    IsReflexive R M where
  bijective_dual_eval'.left := (Free.chooseBasis R M).eval_injective
  bijective_dual_eval'.right := range_eq_top.mp (Free.chooseBasis R M).eval_range

variable [IsReflexive R M]
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [Module.Finite R N] [Projective R N] : IsReflexive R N :=
  have ⟨_, f, hf⟩ := Finite.exists_fin' R N
  have ⟨g, H⟩ := projective_lifting_property f .id hf
  .of_split g f H
/-
**Module._root_.Prod.instModuleIsReflexive** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Prod.instModuleIsReflexive [IsReflexive R N] :
    IsReflexive R (M × N) where
  bijective_dual_eval' := by
    let e : Dual R (Dual R (M × N)) ≃ₗ[R] Dual R (Dual R M) × Dual R (Dual R N) :=
      (dualProdDualEquivDual R M N).dualMap.trans
        (dualProdDualEquivDual R (Dual R M) (Dual R N)).symm
    have : Dual.eval R (M × N) = e.symm.comp ((Dual.eval R M).prodMap (Dual.eval R N)) := by
      ext m f <;> simp [e]
    simp only [this,
      coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective]
    exact (bijective_dual_eval R M).prodMap (bijective_dual_eval R N)
/-
**Module._root_.ULift.instModuleIsReflexive.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.ULift.instModuleIsReflexive.{w} : IsReflexive R (ULift.{w} M) :=
  equiv ULift.moduleEquiv.symm

-- Very low priority because instance resolution will often end up using the instances above
-- to prove `IsReflexive`, which require proving `Finite` again.
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) instFiniteDimensionalOfIsReflexive (K V : Type*)
    [Field K] [AddCommGroup V] [Module K V] [IsReflexive K V] :
    FiniteDimensional K V := by
  rw [FiniteDimensional, ← rank_lt_aleph0_iff]
  by_contra! contra
  suffices lift (Module.rank K V) < Module.rank K (Dual K (Dual K V)) by
    have heq := lift_rank_eq_of_equiv_equiv (R := K) (R' := K) (M := V) (M' := Dual K (Dual K V))
      (ZeroHom.id K) (evalEquiv K V) bijective_id (fun r v ↦ (evalEquiv K V).map_smul _ _)
    rw [← lift_umax, heq, lift_id'] at this
    exact lt_irrefl _ this
  have h₁ : lift (Module.rank K V) < Module.rank K (Dual K V) := lift_rank_lt_rank_dual contra
  have h₂ : Module.rank K (Dual K V) < Module.rank K (Dual K (Dual K V)) := by
    convert! lift_rank_lt_rank_dual <| le_trans (by simpa) h₁.le
    rw [lift_id']
  exact lt_trans h₁ h₂

end IsReflexive

end Module

namespace Submodule

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Submodule R M}

@[simp]
/-
**Submodule.dualCoannihilator_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualCoannihilator_top [Projective R M] : (⊤ : Submodule R (Module.Dual R M
)).dualCoannihilator = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.dualCoannihilator.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst 
: CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (Φ :
 Submodule R (Module.D…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.dualAnnihilator_top`：dualAnnihilator_top : (⊤ : Submodule R M)
.dualAnnihilator = ⊥
· 使用定理 `Submodule.comap_bot`：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
· 使用定理 `Module.eval_ker`：eval_ker : LinearMap.ker (eval K V) = ⊥
-/
theorem dualCoannihilator_top [Projective R M] :
    (⊤ : Submodule R (Module.Dual R M)).dualCoannihilator = ⊥ := by
  rw [dualCoannihilator, dualAnnihilator_top, comap_bot, Module.eval_ker]
/-
**Submodule.exists_dual_map_eq_bot_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：exists_dual_map_eq_bot_of_notMem {R M : Type*} [Ring R] [AddCommGroup M] [
Module R M] {p : Submodule R M} {x : M} (hx : x ∉ p) (hp' : Projective R (M ⧸ p)
) : exists f : Dual R M, f x != 0 ∧ p.map f = ⊥
参数：hx : x ∉ p；hp' : Projective R (M ⧸ p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.exists_dual_ne_zero`：∀ {V : Type uV} [inst : AddCommMo
noid V] (R : Type u_1) [inst_1 : Semiring R] [inst_2 : _root_.Module R V]   [Mod
ule.Projective R V] {x : V}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.mkQ_map_self`：mkQ_map_self : map p.mkQ p = ⊥
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_dual_map_eq_bot_of_notMem
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}
    {x : M} (hx : x ∉ p) (hp' : Projective R (M ⧸ p)) :
    ∃ f : Dual R M, f x ≠ 0 ∧ p.map f = ⊥ := by
  suffices ∃ f : Dual R (M ⧸ p), f (p.mkQ x) ≠ 0 by
    obtain ⟨f, hf⟩ := this; exact ⟨f.comp p.mkQ, hf, by simp [Submodule.map_comp]⟩
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply] at hx
  exact Projective.exists_dual_ne_zero R hx
/-
**Submodule.exists_dual_map_eq_bot_of_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：exists_dual_map_eq_bot_of_lt_top {R M : Type*} [Ring R] [AddCommGroup M] [
Module R M] {p : Submodule R M} (hp : p < ⊤) (hp' : Projective R (M ⧸ p)) : exis
ts f : Dual R M, f != 0 ∧ p.map f = ⊥
参数：hp : p < ⊤；hp' : Projective R (M ⧸ p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Submodule.exists_dual_map_eq_bot_of_notMem`：exists_dual_map_eq_bot_of_no
tMem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M} {x
 : M} (hx : x ∉ p) (hp' : Projec…
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_dual_map_eq_bot_of_lt_top
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}
    (hp : p < ⊤) (hp' : Projective R (M ⧸ p)) :
    ∃ f : Dual R M, f ≠ 0 ∧ p.map f = ⊥ := by
  obtain ⟨x, hx⟩ : ∃ x : M, x ∉ p := by rw [lt_top_iff_ne_top] at hp; contrapose! hp; ext; simp [hp]
  obtain ⟨f, hf, hf'⟩ := p.exists_dual_map_eq_bot_of_notMem hx hp'
  exact ⟨f, by aesop, hf'⟩

/-- Consider a reflexive module and a set `s` of linear forms. If for any `z ≠ 0` there exists
`f ∈ s` such that `f z ≠ 0`, then `s` spans the whole dual space. -/
/-
**Submodule.span_eq_top_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_eq_top_of_ne_zero [IsReflexive R M] {s : Set (M ->ₗ[R] R)} [Projectiv
e R ((M ->ₗ[R] R) ⧸ (span R s))] (h : forall z != 0, exists f in s, f z != 0) : 
span R s = ⊤
参数：M ->ₗ[R] R；(M ->ₗ[R] R) ⧸ (span R s)；h : forall z != 0, exists f in s, f z !=
 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Submodule.exists_dual_map_eq_bot_of_lt_top`：exists_dual_map_eq_bot_of_lt
_top {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M} (h
p : p < ⊤) (hp' : Projective R (…
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Module.apply_evalEquiv_symm_apply`：∀ (R : Type u_3) (M : Type u_4) [inst
 : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [in
st_3 : Module.IsReflexi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
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
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Consider a reflexive module and a set `s` of linear forms. If for any `z ≠ 0` th
ere exists
`f ∈ s` such that `f z ≠ 0`, then `s` spans the whole dual space.
-/
theorem span_eq_top_of_ne_zero [IsReflexive R M]
    {s : Set (M →ₗ[R] R)} [Projective R ((M →ₗ[R] R) ⧸ (span R s))]
    (h : ∀ z ≠ 0, ∃ f ∈ s, f z ≠ 0) : span R s = ⊤ := by
  by_contra! hn
  obtain ⟨φ, φne, hφ⟩ := exists_dual_map_eq_bot_of_lt_top hn.lt_top inferInstance
  let φs := (evalEquiv R M).symm φ
  have this f (hf : f ∈ s) : f φs = 0 := by
    rw [← mem_bot R, ← hφ, mem_map]
    exact ⟨f, subset_span hf, (apply_evalEquiv_symm_apply R M f φ).symm⟩
  obtain ⟨x, xs, hx⟩ := h φs (by simp [φne, φs])
  exact hx <| this x xs

variable {ι 𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

open LinearMap Set FiniteDimensional
/-
**Submodule._root_.FiniteDimensional.mem_span_of_iInf_ker_le_ker** 是 Mathlib 中的一
个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.FiniteDimensional.mem_span_of_iInf_ker_le_ker [FiniteDimensional 𝕜 E]
    {L : ι → E →ₗ[𝕜] 𝕜} {K : E →ₗ[𝕜] 𝕜}
    (h : ⨅ i, LinearMap.ker (L i) ≤ ker K) : K ∈ span 𝕜 (range L) := by
  by_contra hK
  rcases exists_dual_map_eq_bot_of_notMem hK inferInstance with ⟨φ, φne, hφ⟩
  let φs := (Module.evalEquiv 𝕜 E).symm φ
  have : K φs = 0 := by
    refine h <| (Submodule.mem_iInf _).2 fun i ↦ (mem_bot 𝕜).1 ?_
    rw [← hφ, Submodule.mem_map]
    exact ⟨L i, Submodule.subset_span ⟨i, rfl⟩, (apply_evalEquiv_symm_apply 𝕜 E _ φ).symm⟩
  simp only [apply_evalEquiv_symm_apply, φs, φne] at this

/-- Given some linear forms $L_1, ..., L_n, K$ over a vector space $E$, if
$\bigcap_{i=1}^n \mathrm{ker}(L_i) \subseteq \mathrm{ker}(K)$, then $K$ is in the space generated
by $L_1, ..., L_n$. -/
/-
**Submodule._root_.mem_span_of_iInf_ker_le_ker** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given some linear forms $L_1, ..., L_n, K$ over a vector space $E$, if
$\bigcap_{i=1}^n \mathrm{ker}(L_i) \subseteq \mathrm{ker}(K)$, then $K$ is in th
e space generated
by $L_1, ..., L_n$.
-/
theorem _root_.mem_span_of_iInf_ker_le_ker [Finite ι] {L : ι → E →ₗ[𝕜] 𝕜} {K : E →ₗ[𝕜] 𝕜}
    (h : ⨅ i, ker (L i) ≤ ker K) : K ∈ span 𝕜 (range L) := by
  have _ := Fintype.ofFinite ι
  let φ : E →ₗ[𝕜] ι → 𝕜 := LinearMap.pi L
  let p := ⨅ i, ker (L i)
  have p_eq : p = ker φ := (ker_pi L).symm
  let ψ : (E ⧸ p) →ₗ[𝕜] ι → 𝕜 := p.liftQ φ p_eq.le
  have _ : FiniteDimensional 𝕜 (E ⧸ p) := of_injective ψ (ker_eq_bot.1 (ker_liftQ_eq_bot' p φ p_eq))
  let L' i : (E ⧸ p) →ₗ[𝕜] 𝕜 := p.liftQ (L i) (iInf_le _ i)
  let K' : (E ⧸ p) →ₗ[𝕜] 𝕜 := p.liftQ K h
  have : ⨅ i, ker (L' i) ≤ ker K' := by
    simp_rw +zetaDelta [← ker_pi, pi_liftQ_eq_liftQ_pi, ker_liftQ_eq_bot' p φ p_eq]
    exact bot_le
  obtain ⟨c, hK'⟩ :=
    (mem_span_range_iff_exists_fun 𝕜).1 (FiniteDimensional.mem_span_of_iInf_ker_le_ker this)
  refine (mem_span_range_iff_exists_fun 𝕜).2 ⟨c, ?_⟩
  conv_lhs => enter [2]; intro i; rw [← p.liftQ_mkQ (L i) (iInf_le _ i)]
  rw [← p.liftQ_mkQ K h]
  ext x
  convert! LinearMap.congr_fun hK' (p.mkQ x)
  simp only [L', LinearMap.coe_sum, Finset.sum_apply, smul_apply, coe_comp, Function.comp_apply,
    smul_eq_mul]

end Submodule

namespace Subspace

open Submodule LinearMap

-- We work in vector spaces because `exists_isCompl` only hold for vector spaces
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[simp]
/-
**Subspace.dualAnnihilator_dualCoannihilator_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subsp
ace`。
形式化陈述：dualAnnihilator_dualCoannihilator_eq {W : Subspace K V} : W.dualAnnihilato
r.dualCoannihilator = W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Function.mtr`：∀ {a b : Prop}, (¬a → ¬b) → b → a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Module.forall_dual_apply_eq_zero_iff`：forall_dual_apply_eq_zero_iff (R :
 Type*) [Semiring R] [Module R V] [Projective R V] (v : V) : (forall φ : Module.
Dual R V, φ v = 0) ↔ v = 0
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Submodule.le_dualAnnihilator_dualCoannihilator`：le_dualAnnihilator_dualC
oannihilator (U : Submodule R M) : U <= U.dualAnnihilator.dualCoannihilator
-/
theorem dualAnnihilator_dualCoannihilator_eq {W : Subspace K V} :
    W.dualAnnihilator.dualCoannihilator = W := by
  refine le_antisymm (fun v ↦ Function.mtr ?_) (le_dualAnnihilator_dualCoannihilator _)
  simp only [mem_dualAnnihilator, mem_dualCoannihilator]
  rw [← Quotient.mk_eq_zero W, ← Module.forall_dual_apply_eq_zero_iff K]
  push Not
  refine fun ⟨φ, hφ⟩ ↦ ⟨φ.comp W.mkQ, fun w hw ↦ ?_, hφ⟩
  rw [comp_apply, mkQ_apply, (Quotient.mk_eq_zero W).mpr hw, φ.map_zero]

-- exact elaborates slowly
/-
**Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空
间 `Subspace`。
形式化陈述：forall_mem_dualAnnihilator_apply_eq_zero_iff (W : Subspace K V) (v : V) : 
(forall φ : Module.Dual K V, φ in W.dualAnnihilator -> φ v = 0) ↔ v in W
参数：W : Subspace K V；v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Subspace.dualAnnihilator_dualCoannihilator_eq`：dualAnnihilator_dualCoann
ihilator_eq {W : Subspace K V} : W.dualAnnihilator.dualCoannihilator = W
· 使用定理 `Submodule.mem_dualCoannihilator`：mem_dualCoannihilator {Φ : Submodule R 
(Module.Dual R M)} (x : M) : x in Φ.dualCoannihilator ↔ forall φ in Φ, (φ x : R)
 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem forall_mem_dualAnnihilator_apply_eq_zero_iff (W : Subspace K V) (v : V) :
    (∀ φ : Module.Dual K V, φ ∈ W.dualAnnihilator → φ v = 0) ↔ v ∈ W := by
  rw [← SetLike.ext_iff.mp dualAnnihilator_dualCoannihilator_eq v, mem_dualCoannihilator]
/-
**Subspace.comap_dualAnnihilator_dualAnnihilator** 是 Mathlib 中的一个定理，位于命名空间 `Subs
pace`。
形式化陈述：comap_dualAnnihilator_dualAnnihilator (W : Subspace K V) : W.dualAnnihilat
or.dualAnnihilator.comap (Module.Dual.eval K V) = W
参数：W : Subspace K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`：forall_mem_dualAn
nihilator_apply_eq_zero_iff (W : Subspace K V) (v : V) : (forall φ : Module.Dual
 K V, φ in W.dualAnnihilator -> φ v = 0) ↔ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_dualAnnihilator_dualAnnihilator (W : Subspace K V) :
    W.dualAnnihilator.dualAnnihilator.comap (Module.Dual.eval K V) = W := by
  ext; rw [Iff.comm, ← forall_mem_dualAnnihilator_apply_eq_zero_iff]; simp
/-
**Subspace.map_le_dualAnnihilator_dualAnnihilator** 是 Mathlib 中的一个定理，位于命名空间 `Sub
space`。
形式化陈述：map_le_dualAnnihilator_dualAnnihilator (W : Subspace K V) : W.map (Module.
Dual.eval K V) <= W.dualAnnihilator.dualAnnihilator
参数：W : Subspace K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subspace.comap_dualAnnihilator_dualAnnihilator`：comap_dualAnnihilator_du
alAnnihilator (W : Subspace K V) : W.dualAnnihilator.dualAnnihilator.comap (Modu
le.Dual.eval K V) = W
-/
theorem map_le_dualAnnihilator_dualAnnihilator (W : Subspace K V) :
    W.map (Module.Dual.eval K V) ≤ W.dualAnnihilator.dualAnnihilator :=
  map_le_iff_le_comap.mpr (comap_dualAnnihilator_dualAnnihilator W).ge

/-- `Submodule.dualAnnihilator` and `Submodule.dualCoannihilator` form a Galois coinsertion. -/
/-
**Subspace.dualAnnihilatorGci** 是 Mathlib 中的一个定义，位于命名空间 `Subspace`。
形式化陈述：dualAnnihilatorGci (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
 GaloisCoinsertion (OrderDual.toDual ∘ (dualAnnihilator : Subspace K V -> Subspa
ce K (Module.Dual K V))) (dualCoannihilator ∘ OrderDual.ofDual) where choice W _
参数：K V : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Submodule.dualAnnihilator` and `Submodule.dualCoannihilator` form a Galois coin
sertion.
-/
def dualAnnihilatorGci (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    GaloisCoinsertion
      (OrderDual.toDual ∘ (dualAnnihilator : Subspace K V → Subspace K (Module.Dual K V)))
      (dualCoannihilator ∘ OrderDual.ofDual) where
  choice W _ := dualCoannihilator W
  gc := dualAnnihilator_gc K V
  u_l_le _ := dualAnnihilator_dualCoannihilator_eq.le
  choice_eq _ _ := rfl
/-
**Subspace.dualAnnihilator_le_dualAnnihilator_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sub
space`。
形式化陈述：dualAnnihilator_le_dualAnnihilator_iff {W W' : Subspace K V} : W.dualAnnih
ilator <= W'.dualAnnihilator ↔ W' <= W
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.l_le_l_iff`：∀ {α : Type u} {β : Type v} {u : α → β} {l
 : β → α} [inst : Preorder α] [inst_1 : Preorder β]   (gi : GaloisCoinsertion l 
u) {a b : β}, l b …
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem dualAnnihilator_le_dualAnnihilator_iff {W W' : Subspace K V} :
    W.dualAnnihilator ≤ W'.dualAnnihilator ↔ W' ≤ W :=
  (dualAnnihilatorGci K V).l_le_l_iff
/-
**Subspace.dualAnnihilator_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualAnnihilator_inj {W W' : Subspace K V} : W.dualAnnihilator = W'.dualAnn
ihilator ↔ W = W'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `GaloisCoinsertion.l_injective`：∀ {α : Type u} {β : Type v} {u : α → β} {
l : β → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinserti
on l u), Function.I…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem dualAnnihilator_inj {W W' : Subspace K V} :
    W.dualAnnihilator = W'.dualAnnihilator ↔ W = W' :=
  ⟨fun h ↦ (dualAnnihilatorGci K V).l_injective h, congr_arg _⟩

/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dualLift W φ` is
an arbitrary extension of `φ` to an element of the dual of `V`.
That is, `dualLift W φ` sends `w ∈ W` to `φ x` and `x` in a chosen complement of `W` to `0`. -/
/-
**Subspace.dualLift** 是 Mathlib 中的一个定义，位于命名空间 `Subspace`。
形式化陈述：dualLift (W : Subspace K V) : Module.Dual K W ->ₗ[K] Module.Dual K V
参数：W : Subspace K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subspace `W` of `V` and an element of its dual `φ`, `dualLift W φ` is
an arbitrary extension of `φ` to an element of the dual of `V`.
That is, `dualLift W φ` sends `w ∈ W` to `φ x` and `x` in a chosen complement of
 `W` to `0`.
-/
noncomputable def dualLift (W : Subspace K V) : Module.Dual K W →ₗ[K] Module.Dual K V :=
  W.subtype.leftInverse.dualMap

variable {W : Subspace K V}

@[simp]
/-
**Subspace.dualLift_of_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualLift_of_subtype {φ : Module.Dual K W} (w : W) : W.dualLift φ (w : V) =
 φ w
参数：w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LinearMap.leftInverse_apply_of_inj`：LinearMap.leftInverse_apply_of_inj {
f : V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) (x : V) : f.leftInverse (f x) = x
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
-/
theorem dualLift_of_subtype {φ : Module.Dual K W} (w : W) : W.dualLift φ (w : V) = φ w :=
  congr_arg φ <| LinearMap.leftInverse_apply_of_inj W.ker_subtype _
/-
**Subspace.dualLift_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualLift_of_mem {φ : Module.Dual K W} {w : V} (hw : w in W) : W.dualLift φ
 w = φ ⟨w, hw⟩
参数：hw : w in W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subspace.dualLift_of_subtype`：dualLift_of_subtype {φ : Module.Dual K W} 
(w : W) : W.dualLift φ (w : V) = φ w
-/
theorem dualLift_of_mem {φ : Module.Dual K W} {w : V} (hw : w ∈ W) : W.dualLift φ w = φ ⟨w, hw⟩ :=
  dualLift_of_subtype ⟨w, hw⟩

@[simp]
/-
**Subspace.dualRestrict_comp_dualLift** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualRestrict_comp_dualLift (W : Subspace K V) : W.dualRestrict.comp W.dual
Lift = 1
参数：W : Subspace K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subspace.dualLift_of_subtype`：dualLift_of_subtype {φ : Module.Dual K W} 
(w : W) : W.dualLift φ (w : V) = φ w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dualRestrict_comp_dualLift (W : Subspace K V) : W.dualRestrict.comp W.dualLift = 1 := by
  ext φ x
  simp
/-
**Subspace.dualRestrict_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualRestrict_leftInverse (W : Subspace K V) : Function.LeftInverse W.dualR
estrict W.dualLift
参数：W : Subspace K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Subspace.dualRestrict_comp_dualLift`：dualRestrict_comp_dualLift (W : Sub
space K V) : W.dualRestrict.comp W.dualLift = 1
· 使用定理 `Module.End.one_apply`：one_apply (x : M) : (1 : Module.End R M) x = x
-/
theorem dualRestrict_leftInverse (W : Subspace K V) :
    Function.LeftInverse W.dualRestrict W.dualLift := fun x => by
  rw [← LinearMap.comp_apply, dualRestrict_comp_dualLift, End.one_apply]
/-
**Subspace.dualLift_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualLift_rightInverse (W : Subspace K V) : Function.RightInverse W.dualLif
t W.dualRestrict
参数：W : Subspace K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subspace.dualRestrict_leftInverse`：dualRestrict_leftInverse (W : Subspac
e K V) : Function.LeftInverse W.dualRestrict W.dualLift
-/
theorem dualLift_rightInverse (W : Subspace K V) :
    Function.RightInverse W.dualLift W.dualRestrict :=
  W.dualRestrict_leftInverse
/-
**Subspace.dualRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualRestrict_surjective : Function.Surjective W.dualRestrict
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Subspace.dualLift_rightInverse`：dualLift_rightInverse (W : Subspace K V)
 : Function.RightInverse W.dualLift W.dualRestrict
-/
theorem dualRestrict_surjective : Function.Surjective W.dualRestrict :=
  W.dualLift_rightInverse.surjective
/-
**Subspace.dualLift_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualLift_injective : Function.Injective W.dualLift
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Subspace.dualRestrict_leftInverse`：dualRestrict_leftInverse (W : Subspac
e K V) : Function.LeftInverse W.dualRestrict W.dualLift
-/
theorem dualLift_injective : Function.Injective W.dualLift :=
  W.dualRestrict_leftInverse.injective

/-- The quotient by the `dualAnnihilator` of a subspace is isomorphic to the
  dual of that subspace. -/
/-
**Subspace.quotAnnihilatorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subspace`。
形式化陈述：quotAnnihilatorEquiv (W : Subspace K V) : (Module.Dual K V ⧸ W.dualAnnihil
ator) ≃ₗ[K] Module.Dual K W
参数：W : Subspace K V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subspace.dualRestrict_surjective`：dualRestrict_surjective : Function.Sur
jective W.dualRestrict

--- 原说明 ---
The quotient by the `dualAnnihilator` of a subspace is isomorphic to the
  dual of that subspace.
-/
noncomputable def quotAnnihilatorEquiv (W : Subspace K V) :
    (Module.Dual K V ⧸ W.dualAnnihilator) ≃ₗ[K] Module.Dual K W :=
  (quotEquivOfEq _ _ W.dualRestrict_ker_eq_dualAnnihilator).symm.trans <|
    W.dualRestrict.quotKerEquivOfSurjective dualRestrict_surjective

@[simp]
/-
**Subspace.quotAnnihilatorEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：quotAnnihilatorEquiv_apply (W : Subspace K V) (φ : Module.Dual K V) : W.qu
otAnnihilatorEquiv (Submodule.Quotient.mk φ) = W.dualRestrict φ
参数：W : Subspace K V；φ : Module.Dual K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem quotAnnihilatorEquiv_apply (W : Subspace K V) (φ : Module.Dual K V) :
    W.quotAnnihilatorEquiv (Submodule.Quotient.mk φ) = W.dualRestrict φ := by
  ext
  rfl

/-- The natural isomorphism from the dual of a subspace `W` to `W.dualLift.range`. -/
/-
**Subspace.dualEquivDual** 是 Mathlib 中的一个定义，位于命名空间 `Subspace`。
形式化陈述：dualEquivDual (W : Subspace K V) : Module.Dual K W ≃ₗ[K] LinearMap.range W
.dualLift
参数：W : Subspace K V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subspace.dualLift_injective`：dualLift_injective : Function.Injective W.d
ualLift

--- 原说明 ---
The natural isomorphism from the dual of a subspace `W` to `W.dualLift.range`.
-/
noncomputable def dualEquivDual (W : Subspace K V) :
    Module.Dual K W ≃ₗ[K] LinearMap.range W.dualLift :=
  LinearEquiv.ofInjective _ dualLift_injective
/-
**Subspace.dualEquivDual_def** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualEquivDual_def (W : Subspace K V) : W.dualEquivDual.toLinearMap = W.dua
lLift.rangeRestrict
参数：W : Subspace K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualEquivDual_def (W : Subspace K V) :
    W.dualEquivDual.toLinearMap = W.dualLift.rangeRestrict :=
  rfl

@[simp]
/-
**Subspace.dualEquivDual_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualEquivDual_apply (φ : Module.Dual K W) : W.dualEquivDual φ = ⟨W.dualLif
t φ, mem_range.2 ⟨φ, rfl⟩⟩
参数：φ : Module.Dual K W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualEquivDual_apply (φ : Module.Dual K W) :
    W.dualEquivDual φ = ⟨W.dualLift φ, mem_range.2 ⟨φ, rfl⟩⟩ :=
  rfl

section

open FiniteDimensional Module

/-
**Subspace.instModuleDualFiniteDimensional** 是 Mathlib 中的一个实例，位于命名空间 `Subspace`。
形式化陈述：instModuleDualFiniteDimensional [FiniteDimensional K V] : FiniteDimensiona
l K (Module.Dual K V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
instance instModuleDualFiniteDimensional [FiniteDimensional K V] :
    FiniteDimensional K (Module.Dual K V) := by
  infer_instance

@[simp]
/-
**Subspace.dual_finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_eq_zero_of_basis_imp_false`：finrank_eq_zero_of_basis_imp_false (
h : forall s : Finset M, Basis.{v} (s : Set M) R M -> False) : finrank R M = 0
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.finite_dual_iff`：finite_dual_iff [Free K V] : Module.Finite K (Du
al K V) ↔ Module.Finite K V
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
-/
theorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V := by
  by_cases h : FiniteDimensional K V
  · classical exact LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm
  rw [finrank_eq_zero_of_basis_imp_false, finrank_eq_zero_of_basis_imp_false]
  · exact fun _ b ↦ h (Module.Finite.of_basis b)
  · exact fun _ b ↦ h ((Module.finite_dual_iff K).mp <| Module.Finite.of_basis b)

variable [FiniteDimensional K V]
/-
**Subspace.dualAnnihilator_dualAnnihilator_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subspac
e`。
形式化陈述：dualAnnihilator_dualAnnihilator_eq (W : Subspace K V) : W.dualAnnihilator.
dualAnnihilator = Module.mapEvalEquiv K V W
参数：W : Subspace K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subspace.dualAnnihilator_dualCoannihilator_eq`：dualAnnihilator_dualCoann
ihilator_eq {W : Subspace K V} : W.dualAnnihilator.dualCoannihilator = W
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.instIsReflexiveOfFiniteOfProjective`：∀ (R : Type u_1) (N : Type u
_3) [inst : CommSemiring R] [inst_1 : AddCommMonoid N] [inst_2 : _root_.Module R
 N]   [Module.Finite R N] [Modul…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.symm_apply_eq`：symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.s
ymm y = x ↔ y = e x
· 使用定理 `Module.mapEvalEquiv_symm_apply`：mapEvalEquiv_symm_apply (W'' : Submodule
 R (Dual R (Dual R M))) : (mapEvalEquiv R M).symm W'' = W''.comap (Dual.eval R M
)
· 使用定理 `Submodule.dualCoannihilator.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst 
: CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (Φ :
 Submodule R (Module.D…
-/
theorem dualAnnihilator_dualAnnihilator_eq (W : Subspace K V) :
    W.dualAnnihilator.dualAnnihilator = Module.mapEvalEquiv K V W := by
  have : _ = W := Subspace.dualAnnihilator_dualCoannihilator_eq
  rw [dualCoannihilator, ← Module.mapEvalEquiv_symm_apply] at this
  rwa [← OrderIso.symm_apply_eq]

/-- The quotient by the dual is isomorphic to its dual annihilator. -/
/-
**Subspace.quotDualEquivAnnihilator** 是 Mathlib 中的一个定义，位于命名空间 `Subspace`。
形式化陈述：quotDualEquivAnnihilator (W : Subspace K V) : (Module.Dual K V ⧸ LinearMap
.range W.dualLift) ≃ₗ[K] W.dualAnnihilator
参数：W : Subspace K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient by the dual is isomorphic to its dual annihilator.
-/
noncomputable def quotDualEquivAnnihilator (W : Subspace K V) :
    (Module.Dual K V ⧸ LinearMap.range W.dualLift) ≃ₗ[K] W.dualAnnihilator :=
  LinearEquiv.quotEquivOfQuotEquiv <| LinearEquiv.trans W.quotAnnihilatorEquiv W.dualEquivDual

open scoped Classical in
/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
/-
**Subspace.quotEquivAnnihilator** 是 Mathlib 中的一个定义，位于命名空间 `Subspace`。
形式化陈述：quotEquivAnnihilator (W : Subspace K V) : (V ⧸ W) ≃ₗ[K] W.dualAnnihilator
参数：W : Subspace K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient by a subspace is isomorphic to its dual annihilator.
-/
noncomputable def quotEquivAnnihilator (W : Subspace K V) : (V ⧸ W) ≃ₗ[K] W.dualAnnihilator :=
  let φ := (Basis.ofVectorSpace K W).toDualEquiv.trans W.dualEquivDual
  let ψ := LinearEquiv.quotEquivOfEquiv φ (Basis.ofVectorSpace K V).toDualEquiv
  ψ ≪≫ₗ W.quotDualEquivAnnihilator

open Module
/-
**Subspace.finrank_add_finrank_dualAnnihilator_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sub
space`。
形式化陈述：finrank_add_finrank_dualAnnihilator_eq (W : Subspace K V) : finrank K W + 
finrank K W.dualAnnihilator = finrank K V
参数：W : Subspace K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Submodule.finrank_quotient_add_finrank`：Submodule.finrank_quotient_add_f
inrank [Module.Finite R M] (N : Submodule R M) : finrank R (M ⧸ N) + finrank R N
 = finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem finrank_add_finrank_dualAnnihilator_eq (W : Subspace K V) :
    finrank K W + finrank K W.dualAnnihilator = finrank K V := by
  rw [← W.quotEquivAnnihilator.finrank_eq, add_comm, Submodule.finrank_quotient_add_finrank]

@[simp]
/-
**Subspace.finrank_dualCoannihilator_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：finrank_dualCoannihilator_eq {Φ : Subspace K (Module.Dual K V)} : finrank 
K Φ.dualCoannihilator = finrank K Φ.dualAnnihilator
参数：Module.Dual K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.dualCoannihilator.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst 
: CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (Φ :
 Submodule R (Module.D…
· 使用定理 `Module.instIsReflexiveOfFiniteOfProjective`：∀ (R : Type u_1) (N : Type u
_3) [inst : CommSemiring R] [inst_1 : AddCommMonoid N] [inst_2 : _root_.Module R
 N]   [Module.Finite R N] [Modul…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.evalEquiv_toLinearMap`：∀ (R : Type u_3) (M : Type u_4) [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 
: Module.IsReflexi…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
theorem finrank_dualCoannihilator_eq {Φ : Subspace K (Module.Dual K V)} :
    finrank K Φ.dualCoannihilator = finrank K Φ.dualAnnihilator := by
  rw [Submodule.dualCoannihilator, ← Module.evalEquiv_toLinearMap]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' _ _)
/-
**Subspace.finrank_add_finrank_dualCoannihilator_eq** 是 Mathlib 中的一个定理，位于命名空间 `S
ubspace`。
形式化陈述：finrank_add_finrank_dualCoannihilator_eq (W : Subspace K (Module.Dual K V)
) : finrank K W + finrank K W.dualCoannihilator = finrank K V
参数：W : Subspace K (Module.Dual K V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subspace.finrank_dualCoannihilator_eq`：finrank_dualCoannihilator_eq {Φ :
 Subspace K (Module.Dual K V)} : finrank K Φ.dualCoannihilator = finrank K Φ.dua
lAnnihilator
· 使用定理 `Subspace.finrank_add_finrank_dualAnnihilator_eq`：finrank_add_finrank_dua
lAnnihilator_eq (W : Subspace K V) : finrank K W + finrank K W.dualAnnihilator =
 finrank K V
· 使用定理 `Subspace.dual_finrank_eq`：dual_finrank_eq : finrank K (Module.Dual K V) 
= finrank K V
-/
theorem finrank_add_finrank_dualCoannihilator_eq (W : Subspace K (Module.Dual K V)) :
    finrank K W + finrank K W.dualCoannihilator = finrank K V := by
  rw [finrank_dualCoannihilator_eq, finrank_add_finrank_dualAnnihilator_eq, dual_finrank_eq]

end

end Subspace

open Module

section CommRing

variable {R M M' : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

namespace Submodule

/-- Given a submodule, corestrict to the pairing on `M ⧸ W` by
simultaneously restricting to `W.dualAnnihilator`.

See `Subspace.dualCopairing_nondegenerate`. -/
/-
**Submodule.dualCopairing** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：dualCopairing (W : Submodule R M) : W.dualAnnihilator ->ₗ[R] M ⧸ W ->ₗ[R] 
R
参数：W : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a submodule, corestrict to the pairing on `M ⧸ W` by
simultaneously restricting to `W.dualAnnihilator`.

See `Subspace.dualCopairing_nondegenerate`.
-/
def dualCopairing (W : Submodule R M) : W.dualAnnihilator →ₗ[R] M ⧸ W →ₗ[R] R :=
  LinearMap.flip <| W.liftQ W.dualAnnihilator.subtype.flip (by
    intro w hw
    ext ⟨φ, hφ⟩
    exact (mem_dualAnnihilator φ).mp hφ w hw)
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (W : Submodule R M) : FunLike (W.dualAnnihilator) M R where
  coe φ := φ.val
  coe_injective φ ψ h := by
    ext
    simp only [funext_iff] at h
    exact h _

@[simp]
/-
**Submodule.dualCopairing_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualCopairing_apply {W : Submodule R M} (φ : W.dualAnnihilator) (x : M) : 
W.dualCopairing φ (Quotient.mk x) = φ x
参数：φ : W.dualAnnihilator；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualCopairing_apply {W : Submodule R M} (φ : W.dualAnnihilator) (x : M) :
    W.dualCopairing φ (Quotient.mk x) = φ x :=
  rfl

/-- Given a submodule, restrict to the pairing on `W` by
simultaneously corestricting to `Module.Dual R M ⧸ W.dualAnnihilator`.
This is `Submodule.dualRestrict` factored through the quotient by its kernel (which
is `W.dualAnnihilator` by definition).

See `Subspace.dualPairing_nondegenerate`. -/
/-
**Submodule.dualPairing** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：dualPairing (W : Submodule R M) : Module.Dual R M ⧸ W.dualAnnihilator ->ₗ[
R] W ->ₗ[R] R
参数：W : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a submodule, restrict to the pairing on `W` by
simultaneously corestricting to `Module.Dual R M ⧸ W.dualAnnihilator`.
This is `Submodule.dualRestrict` factored through the quotient by its kernel (wh
ich
is `W.dualAnnihilator` by definition).

See `Subspace.dualPairing_nondegenerate`.
-/
def dualPairing (W : Submodule R M) : Module.Dual R M ⧸ W.dualAnnihilator →ₗ[R] W →ₗ[R] R :=
  W.dualAnnihilator.liftQ W.dualRestrict le_rfl

@[simp]
/-
**Submodule.dualPairing_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualPairing_apply {W : Submodule R M} (φ : Module.Dual R M) (x : W) : W.du
alPairing (Quotient.mk φ) x = φ x
参数：φ : Module.Dual R M；x : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualPairing_apply {W : Submodule R M} (φ : Module.Dual R M) (x : W) :
    W.dualPairing (Quotient.mk φ) x = φ x :=
  rfl

/-- That $\operatorname{im}(q^* : (V/W)^* \to V^*) = \operatorname{ann}(W)$. -/
/-
**Submodule.range_dualMap_mkQ_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_dualMap_mkQ_eq (W : Submodule R M) : LinearMap.range W.mkQ.dualMap =
 W.dualAnnihilator
参数：W : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `LinearMap.range_dualMap_le_dualAnnihilator_ker`：range_dualMap_le_dualAnn
ihilator_ker : LinearMap.range f.dualMap <= (ker f).dualAnnihilator
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
That $\operatorname{im}(q^* : (V/W)^* \to V^*) = \operatorname{ann}(W)$.
-/
theorem range_dualMap_mkQ_eq (W : Submodule R M) :
    LinearMap.range W.mkQ.dualMap = W.dualAnnihilator := by
  ext φ
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨ψ, rfl⟩
    have := LinearMap.mem_range_self W.mkQ.dualMap ψ
    simpa only [ker_mkQ] using W.mkQ.range_dualMap_le_dualAnnihilator_ker this
  · intro hφ
    exists W.dualCopairing ⟨φ, hφ⟩

/-- Equivalence $(M/W)^* \cong \operatorname{ann}(W)$. That is, there is a one-to-one
correspondence between the dual of `M ⧸ W` and those elements of the dual of `M` that
vanish on `W`.

The inverse of this is `Submodule.dualCopairing`. -/
/-
**Submodule.dualQuotEquivDualAnnihilator** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：dualQuotEquivDualAnnihilator (W : Submodule R M) : Module.Dual R (M ⧸ W) ≃
ₗ[R] W.dualAnnihilator
参数：W : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence $(M/W)^* \cong \operatorname{ann}(W)$. That is, there is a one-to-on
e
correspondence between the dual of `M ⧸ W` and those elements of the dual of `M`
 that
vanish on `W`.

The inverse of this is `Submodule.dualCopairing`.
-/
def dualQuotEquivDualAnnihilator (W : Submodule R M) :
    Module.Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator :=
  LinearEquiv.ofLinearMap
    (W.mkQ.dualMap.codRestrict W.dualAnnihilator fun φ =>
      W.range_dualMap_mkQ_eq ▸ LinearMap.mem_range_self W.mkQ.dualMap φ)
    W.dualCopairing (by ext; rfl) (by ext; rfl)

@[simp]
/-
**Submodule.dualQuotEquivDualAnnihilator_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：dualQuotEquivDualAnnihilator_apply (W : Submodule R M) (φ : Module.Dual R 
(M ⧸ W)) (x : M) : dualQuotEquivDualAnnihilator W φ x = φ (Quotient.mk x)
参数：W : Submodule R M；φ : Module.Dual R (M ⧸ W)；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualQuotEquivDualAnnihilator_apply (W : Submodule R M) (φ : Module.Dual R (M ⧸ W)) (x : M) :
    dualQuotEquivDualAnnihilator W φ x = φ (Quotient.mk x) :=
  rfl
/-
**Submodule.dualCopairing_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualCopairing_eq (W : Submodule R M) : W.dualCopairing = (dualQuotEquivDua
lAnnihilator W).symm.toLinearMap
参数：W : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualCopairing_eq (W : Submodule R M) :
    W.dualCopairing = (dualQuotEquivDualAnnihilator W).symm.toLinearMap :=
  rfl

@[simp]
/-
**Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule`。
形式化陈述：dualQuotEquivDualAnnihilator_symm_apply_mk (W : Submodule R M) (φ : W.dual
Annihilator) (x : M) : (dualQuotEquivDualAnnihilator W).symm φ (Quotient.mk x) =
 φ x
参数：W : Submodule R M；φ : W.dualAnnihilator；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualQuotEquivDualAnnihilator_symm_apply_mk (W : Submodule R M) (φ : W.dualAnnihilator)
    (x : M) : (dualQuotEquivDualAnnihilator W).symm φ (Quotient.mk x) = φ x :=
  rfl
/-
**Submodule.finite_dualAnnihilator_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：finite_dualAnnihilator_iff {W : Submodule R M} [Free R (M ⧸ W)] : Module.F
inite R W.dualAnnihilator ↔ Module.Finite R (M ⧸ W)
参数：M ⧸ W。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Finite.equiv_iff`：equiv_iff (e : M ≃ₗ[R] N) : Module.Finite R M ↔
 Module.Finite R N
· 使用定理 `Module.finite_dual_iff`：finite_dual_iff [Free K V] : Module.Finite K (Du
al K V) ↔ Module.Finite K V
-/
theorem finite_dualAnnihilator_iff {W : Submodule R M} [Free R (M ⧸ W)] :
    Module.Finite R W.dualAnnihilator ↔ Module.Finite R (M ⧸ W) :=
  (Finite.equiv_iff W.dualQuotEquivDualAnnihilator.symm).trans (finite_dual_iff R)
/-
**Submodule.dualAnnihilator_eq_bot_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：dualAnnihilator_eq_bot_iff' {W : Submodule R M} : W.dualAnnihilator = ⊥ ↔ 
Subsingleton (Dual R (M ⧸ W))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.subsingleton_iff_eq_bot`：subsingleton_iff_eq_bot : Subsingleto
n p ↔ p = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma dualAnnihilator_eq_bot_iff' {W : Submodule R M} :
    W.dualAnnihilator = ⊥ ↔ Subsingleton (Dual R (M ⧸ W)) := by
  rw [W.dualQuotEquivDualAnnihilator.toEquiv.subsingleton_congr, subsingleton_iff_eq_bot]
/-
**Submodule.dualAnnihilator_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {W : Submodule R M} [Module.Projective R (M ⧸
 W)], W.dualAnnihilator = ⊥ ↔ W = ⊤
参数：M ⧸ W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.dualAnnihilator_eq_bot_iff'`：dualAnnihilator_eq_bot_iff' {W : 
Submodule R M} : W.dualAnnihilator = ⊥ ↔ Subsingleton (Dual R (M ⧸ W))
· 使用定理 `Module.subsingleton_dual_iff`：subsingleton_dual_iff : Subsingleton (Dual
 K V) ↔ Subsingleton V
· 使用定理 `Submodule.Quotient.subsingleton_iff`：∀ {R : Type u_1} {M : Type u_2} [in
st : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submo
dule R M}, Subsingleton (…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma dualAnnihilator_eq_bot_iff {W : Submodule R M} [Projective R (M ⧸ W)] :
    W.dualAnnihilator = ⊥ ↔ W = ⊤ := by
  rw [dualAnnihilator_eq_bot_iff', subsingleton_dual_iff, Quotient.subsingleton_iff]
/-
**Submodule.dualAnnihilator_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {W : Submodule R M} [Module.Projective R M], 
W.dualAnnihilator = ⊤ ↔ W = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.forall_dual_apply_eq_zero_iff`：forall_dual_apply_eq_zero_iff (R :
 Type*) [Semiring R] [Module R V] [Projective R V] (v : V) : (forall φ : Module.
Dual R V, φ v = 0) ↔ v = 0
· 使用定理 `Submodule.mem_dualAnnihilator`：mem_dualAnnihilator (φ : Module.Dual R M)
 : φ in W.dualAnnihilator ↔ forall w in W, φ w = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.dualAnnihilator_bot`：dualAnnihilator_bot : (⊥ : Submodule R M)
.dualAnnihilator = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma dualAnnihilator_eq_top_iff {W : Submodule R M} [Projective R M] :
    W.dualAnnihilator = ⊤ ↔ W = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ dualAnnihilator_bot⟩
  refine W.eq_bot_iff.mpr fun v hv ↦ (forall_dual_apply_eq_zero_iff R v).mp fun f ↦ ?_
  refine (mem_dualAnnihilator f).mp ?_ v hv
  simp [h]

open LinearMap in
/-- The pairing between a submodule `W` of a dual module `Dual R M` and the quotient of
`M` by the coannihilator of `W`, which is always nondegenerate. -/
/-
**Submodule.quotDualCoannihilatorToDual** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotDualCoannihilatorToDual (W : Submodule R (Dual R M)) : M ⧸ W.dualCoann
ihilator ->ₗ[R] Dual R W
参数：W : Submodule R (Dual R M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pairing between a submodule `W` of a dual module `Dual R M` and the quotient
 of
`M` by the coannihilator of `W`, which is always nondegenerate.
-/
def quotDualCoannihilatorToDual (W : Submodule R (Dual R M)) :
    M ⧸ W.dualCoannihilator →ₗ[R] Dual R W :=
  liftQ _ (flip <| Submodule.subtype _) le_rfl

@[simp]
/-
**Submodule.quotDualCoannihilatorToDual_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：quotDualCoannihilatorToDual_apply (W : Submodule R (Dual R M)) (m : M) (w 
: W) : W.quotDualCoannihilatorToDual (Quotient.mk m) w = w.1 m
参数：W : Submodule R (Dual R M)；m : M；w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem quotDualCoannihilatorToDual_apply (W : Submodule R (Dual R M)) (m : M) (w : W) :
    W.quotDualCoannihilatorToDual (Quotient.mk m) w = w.1 m := rfl
/-
**Submodule.quotDualCoannihilatorToDual_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
形式化陈述：quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) : Funct
ion.Injective W.quotDualCoannihilatorToDual
参数：W : Submodule R (Dual R M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.ker_liftQ_eq_bot`：ker_liftQ_eq_bot (f : M ->ₛₗ[τ₁₂] M₂) (h) (h
' : ker f <= p) : ker (p.liftQ f h) = ⊥
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) :
    Function.Injective W.quotDualCoannihilatorToDual :=
  LinearMap.ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ le_rfl)
/-
**Submodule.flip_quotDualCoannihilatorToDual_injective** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule`。
形式化陈述：flip_quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) : 
Function.Injective W.quotDualCoannihilatorToDual.flip
参数：W : Submodule R (Dual R M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem flip_quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) :
    Function.Injective W.quotDualCoannihilatorToDual.flip :=
  fun _ _ he ↦ Subtype.ext <| LinearMap.ext fun m ↦ DFunLike.congr_fun he ⟦m⟧

open LinearMap in
/-
**Submodule.quotDualCoannihilatorToDual_nondegenerate** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule`。
形式化陈述：quotDualCoannihilatorToDual_nondegenerate (W : Submodule R (Dual R M)) : W
.quotDualCoannihilatorToDual.Nondegenerate
参数：W : Submodule R (Dual R M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.Nondegenerate.eq_1`：∀ {R : Type u_1} {R₁ : Type u_2} {R₂ : Typ
e u_3} {M : Type u_5} {M₁ : Type u_6} {M₂ : Type u_7} [inst : CommSemiring R]   
[inst_1 : AddCommM…
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.separatingRight_iff_flip_ker_eq_bot`：separatingRight_iff_flip_
ker_eq_bot {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingRight ↔ LinearMap.ker B
.flip = ⊥
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.quotDualCoannihilatorToDual_injective`：quotDualCoannihilatorTo
Dual_injective (W : Submodule R (Dual R M)) : Function.Injective W.quotDualCoann
ihilatorToDual
· 使用定理 `Submodule.flip_quotDualCoannihilatorToDual_injective`：flip_quotDualCoann
ihilatorToDual_injective (W : Submodule R (Dual R M)) : Function.Injective W.quo
tDualCoannihilatorToDual.flip
-/
theorem quotDualCoannihilatorToDual_nondegenerate (W : Submodule R (Dual R M)) :
    W.quotDualCoannihilatorToDual.Nondegenerate := by
  rw [Nondegenerate, separatingLeft_iff_ker_eq_bot, separatingRight_iff_flip_ker_eq_bot]
  simp_rw [ker_eq_bot]
  exact ⟨W.quotDualCoannihilatorToDual_injective, W.flip_quotDualCoannihilatorToDual_injective⟩

end Submodule

namespace LinearMap

open Submodule

/-
**LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective** 是 Mathlib 中的一个定
理，位于命名空间 `LinearMap`。
形式化陈述：range_dualMap_eq_dualAnnihilator_ker_of_surjective (f : M ->ₗ[R] M') (hf :
 Function.Surjective f) : LinearMap.range f.dualMap = (LinearMap.ker f).dualAnni
hilator
参数：f : M ->ₗ[R] M'；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearEquiv.range_comp`：range_comp [RingHomSurjective σ₂₃] [RingHomSurje
ctive σ₁₃] : LinearMap.range (h.comp (e : M ->ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = Li
nearMap.rang…
· 使用定理 `Submodule.range_dualMap_mkQ_eq`：range_dualMap_mkQ_eq (W : Submodule R M)
 : LinearMap.range W.mkQ.dualMap = W.dualAnnihilator
-/
theorem range_dualMap_eq_dualAnnihilator_ker_of_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective f) : LinearMap.range f.dualMap = (LinearMap.ker f).dualAnnihilator :=
  ((f.quotKerEquivOfSurjective hf).dualMap.range_comp _).trans
    (LinearMap.ker f).range_dualMap_mkQ_eq

-- Note, this can be specialized to the case where `R` is an injective `R`-module, or when
-- `f.coker` is a projective `R`-module.
/-
**LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective** 是
 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective (f : M ->
ₗ[R] M') (hf : Function.Surjective (range f).subtype.dualMap) : LinearMap.range 
f.dualMap = (ker f).dualAnnihilator
参数：f : M ->ₗ[R] M'；hf : Function.Surjective (range f).subtype.dualMap。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.range_rangeRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Typ
e u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
· 使用定理 `LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective`：range_dual
Map_eq_dualAnnihilator_ker_of_surjective (f : M ->ₗ[R] M') (hf : Function.Surjec
tive f) : LinearMap.range f.dualMap = (LinearMap.k…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.dualMap_comp_dualMap`：LinearMap.dualMap_comp_dualMap {M₃ : Typ
e*} [AddCommMonoid M₃] [Module R M₃] (f : M₁ ->ₗ[R] M₂) (g : M₂ ->ₗ[R] M₃) : f.d
ualMap.comp g.dualMa…
· 使用定理 `LinearMap.range_comp_of_range_eq_top`：range_comp_of_range_eq_top [RingHo
mSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] {f : M ->ₛₗ[τ₁₂
] M₂} (g : M₂ ->ₛₗ[τ₂₃] M₃…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LinearMap.ker_rangeRestrict`：ker_rangeRestrict : ker f.rangeRestrict = k
er f
-/
theorem range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective (range f).subtype.dualMap) :
    LinearMap.range f.dualMap = (ker f).dualAnnihilator := by
  have rr_surj : Function.Surjective f.rangeRestrict := by
    rw [← range_eq_top, range_rangeRestrict]
  have := range_dualMap_eq_dualAnnihilator_ker_of_surjective f.rangeRestrict rr_surj
  convert! this using 1
  · calc
      _ = range ((range f).subtype.comp f.rangeRestrict).dualMap := by simp
      _ = _ := ?_
    rw [← dualMap_comp_dualMap, range_comp_of_range_eq_top]
    rwa [range_eq_top]
  · apply congr_arg
    exact (ker_rangeRestrict f).symm

end LinearMap

end CommRing

section VectorSpace

section

variable {K V₁ V₂ : Type*} [DivisionRing K]
variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

namespace Module.Dual

variable {f : Module.Dual K V₁}

section
variable (hf : f ≠ 0)

/-
**Module.Dual.range_eq_top_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Module.Dual`。
形式化陈述：range_eq_top_of_ne_zero {K V₁ : Type*} [DivisionSemiring K] [AddCommMonoid
 V₁] [Module K V₁] {f : Module.Dual K V₁} (hf : f != 0) : LinearMap.range f = ⊤
参数：hf : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.surjective`：∀ {R : Type u_1} {M : Type u_2} [inst : AddCommMon
oid M] [inst_1 : DivisionSemiring R] [inst_2 : _root_.Module R M]   {f : M →ₗ[R]
 R}, f ≠ 0…
-/
lemma range_eq_top_of_ne_zero {K V₁ : Type*} [DivisionSemiring K] [AddCommMonoid V₁] [Module K V₁]
    {f : Module.Dual K V₁} (hf : f ≠ 0) : LinearMap.range f = ⊤ :=
  LinearMap.range_eq_top.mpr (LinearMap.surjective hf)

variable [FiniteDimensional K V₁]
include hf
/-
**Module.Dual.finrank_ker_add_one_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Module.D
ual`。
形式化陈述：finrank_ker_add_one_of_ne_zero : finrank K (LinearMap.ker f) + 1 = finrank
 K V₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Dual.range_eq_top_of_ne_zero`：range_eq_top_of_ne_zero {K V₁ : Typ
e*} [DivisionSemiring K] [AddCommMonoid V₁] [Module K V₁] {f : Module.Dual K V₁}
 (hf : f != 0) : LinearMa…
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.finrank_quotient_add_finrank`：Submodule.finrank_quotient_add_f
inrank [Module.Finite R M] (N : Submodule R M) : finrank R (M ⧸ N) + finrank R N
 = finrank R M
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
lemma finrank_ker_add_one_of_ne_zero :
    finrank K (LinearMap.ker f) + 1 = finrank K V₁ := by
  suffices finrank K (LinearMap.range f) = 1 by
    rw [← (LinearMap.ker f).finrank_quotient_add_finrank, add_comm, add_left_inj,
    f.quotKerEquivRange.finrank_eq, this]
  rw [range_eq_top_of_ne_zero hf, finrank_top, finrank_self]
/-
**Module.Dual.isCompl_ker_of_disjoint_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e.Dual`。
形式化陈述：isCompl_ker_of_disjoint_of_ne_bot {p : Submodule K V₁} (hpf : Disjoint (Li
nearMap.ker f) p) (hp : p != ⊥) : IsCompl (LinearMap.ker f) p
参数：hpf : Disjoint (LinearMap.ker f) p；hp : p != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Submodule.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₂ <= finrank
 K S₁) : S₁ = S₂
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.finrank_sup_add_finrank_inf_eq`：finrank_sup_add_finrank_inf_eq
 (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] : finrank
 K ↑(s ⊔ t) + finrank K ↑(s ⊓ …
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用引理 `Module.Dual.finrank_ker_add_one_of_ne_zero`：finrank_ker_add_one_of_ne_ze
ro : finrank K (LinearMap.ker f) + 1 = finrank K V₁
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用引理 `Submodule.one_le_finrank_iff`：Submodule.one_le_finrank_iff [StrongRankCo
ndition R] {S : Submodule R M} [Module.Finite R S] : 1 <= finrank R S ↔ S != ⊥
-/
lemma isCompl_ker_of_disjoint_of_ne_bot {p : Submodule K V₁}
    (hpf : Disjoint (LinearMap.ker f) p) (hp : p ≠ ⊥) :
    IsCompl (LinearMap.ker f) p := by
  refine ⟨hpf, codisjoint_iff.mpr <| eq_of_le_of_finrank_le le_top ?_⟩
  have : finrank K ↑(LinearMap.ker f ⊔ p) = finrank K (LinearMap.ker f) + finrank K p := by
    simp [← Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) p, hpf.eq_bot]
  rwa [finrank_top, this, ← finrank_ker_add_one_of_ne_zero hf, add_le_add_iff_left,
    Submodule.one_le_finrank_iff]

end

/-
**Module.Dual.eq_of_ker_eq_of_apply_eq** 是 Mathlib 中的一个引理，位于命名空间 `Module.Dual`。
形式化陈述：eq_of_ker_eq_of_apply_eq [FiniteDimensional K V₁] {f g : Module.Dual K V₁}
 (x : V₁) (h : LinearMap.ker f = LinearMap.ker g) (h' : f x = g x) (hx : f x != 
0) : f = g
参数：x : V₁；h : LinearMap.ker f = LinearMap.ker g；h' : f x = g x；hx : f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
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
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用引理 `Module.Dual.isCompl_ker_of_disjoint_of_ne_bot`：isCompl_ker_of_disjoint_o
f_ne_bot {p : Submodule K V₁} (hpf : Disjoint (LinearMap.ker f) p) (hp : p != ⊥)
 : IsCompl (LinearMap.ker f) p
（共 35 条，此处仅展示前 30 条）
-/
lemma eq_of_ker_eq_of_apply_eq [FiniteDimensional K V₁] {f g : Module.Dual K V₁} (x : V₁)
    (h : LinearMap.ker f = LinearMap.ker g) (h' : f x = g x) (hx : f x ≠ 0) :
    f = g := by
  let p := K ∙ x
  have hp : p ≠ ⊥ := by aesop
  have hpf : Disjoint (LinearMap.ker f) p := by
    rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro y ⟨hfy : f y = 0, hpy : y ∈ p⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hpy
    have ht : t = 0 := by simpa [hx] using hfy
    simp [ht]
  have hf : f ≠ 0 := by aesop
  ext v
  obtain ⟨y, hy, z, hz, rfl⟩ : ∃ᵉ (y ∈ LinearMap.ker f) (z ∈ p), y + z = v := by
    have : v ∈ (⊤ : Submodule K V₁) := Submodule.mem_top
    rwa [← (isCompl_ker_of_disjoint_of_ne_bot hf hpf hp).sup_eq_top, Submodule.mem_sup] at this
  have hy' : g y = 0 := by rwa [← LinearMap.mem_ker, ← h]
  replace hy : f y = 0 := by rwa [LinearMap.mem_ker] at hy
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp [h', hy, hy']

end Module.Dual

end

namespace LinearMap

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-
**LinearMap.id_separatingLeft** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：id_separatingLeft : SeparatingLeft (M₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用定理 `LinearMap.ker_id`：ker_id : ker (LinearMap.id : M ->ₗ[R] M) = ⊥
-/
theorem id_separatingLeft : SeparatingLeft (M₁ := V →ₗ[K] K) .id :=
  separatingLeft_iff_ker_eq_bot.mpr ker_id
/-
**LinearMap.eval_separatingRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eval_separatingRight : SeparatingRight (Dual.eval K V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.id_separatingLeft`：id_separatingLeft : SeparatingLeft (M₁
-/
theorem eval_separatingRight : SeparatingRight (Dual.eval K V) := id_separatingLeft

variable [Module.Projective K V]
/-
**LinearMap.id_separatingRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：id_separatingRight : SeparatingRight (M₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.forall_dual_apply_eq_zero_iff`：forall_dual_apply_eq_zero_iff (R :
 Type*) [Semiring R] [Module R V] [Projective R V] (v : V) : (forall φ : Module.
Dual R V, φ v = 0) ↔ v = 0
-/
theorem id_separatingRight : SeparatingRight (M₁ := V →ₗ[K] K) .id :=
  fun x => (forall_dual_apply_eq_zero_iff K x).mp
/-
**LinearMap.eval_separatingLeft** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eval_separatingLeft : SeparatingLeft (Dual.eval K V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.id_separatingRight`：id_separatingRight : SeparatingRight (M₁
-/
theorem eval_separatingLeft : SeparatingLeft (Dual.eval K V) := id_separatingRight
/-
**LinearMap.id_nondegenerate** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：id_nondegenerate : Nondegenerate (M₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.id_separatingLeft`：id_separatingLeft : SeparatingLeft (M₁
· 使用定理 `LinearMap.id_separatingRight`：id_separatingRight : SeparatingRight (M₁
-/
theorem id_nondegenerate : Nondegenerate (M₁ := V →ₗ[K] K) .id :=
  ⟨id_separatingLeft, id_separatingRight⟩

@[deprecated (since := "2026-04-02")]
alias dualPairing_nondegenerate := id_nondegenerate
/-
**LinearMap.eval_nondegenerate** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：eval_nondegenerate : Nondegenerate (Dual.eval K V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.eval_separatingLeft`：eval_separatingLeft : SeparatingLeft (Dua
l.eval K V)
· 使用定理 `LinearMap.eval_separatingRight`：eval_separatingRight : SeparatingRight (
Dual.eval K V)
-/
theorem eval_nondegenerate : Nondegenerate (Dual.eval K V) :=
  ⟨eval_separatingLeft, eval_separatingRight⟩

variable {K V₁ V₂ : Type*} [Field K]
variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
/-
**LinearMap.dualMap_surjective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：dualMap_surjective_of_injective {f : V₁ ->ₗ[K] V₂} (hf : Function.Injectiv
e f) : Function.Surjective f.dualMap
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.exists_leftInverse_of_injective`：LinearMap.exists_leftInverse_
of_injective (f : V ->ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) : exists g : V' ->
ₗ[K] V, g.comp f = LinearMap.id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem dualMap_surjective_of_injective {f : V₁ →ₗ[K] V₂} (hf : Function.Injective f) :
    Function.Surjective f.dualMap := fun φ ↦
  have ⟨f', hf'⟩ := f.exists_leftInverse_of_injective (ker_eq_bot.mpr hf)
  ⟨φ.comp f', ext fun x ↦ congr(φ <| $hf' x)⟩
/-
**LinearMap.range_dualMap_eq_dualAnnihilator_ker** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：range_dualMap_eq_dualAnnihilator_ker (f : V₁ ->ₗ[K] V₂) : LinearMap.range 
f.dualMap = (LinearMap.ker f).dualAnnihilator
参数：f : V₁ ->ₗ[K] V₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjecti
ve`：range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective (f : M ->ₗ[
R] M') (hf : Function.Surjective (range f).subtype.dualMap) : Li…
· 使用定理 `LinearMap.dualMap_surjective_of_injective`：dualMap_surjective_of_injecti
ve {f : V₁ ->ₗ[K] V₂} (hf : Function.Injective f) : Function.Surjective f.dualMa
p
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
-/
theorem range_dualMap_eq_dualAnnihilator_ker (f : V₁ →ₗ[K] V₂) :
    LinearMap.range f.dualMap = (LinearMap.ker f).dualAnnihilator :=
  range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective f <|
    dualMap_surjective_of_injective (range f).injective_subtype

/-- For vector spaces, `f.dualMap` is surjective if and only if `f` is injective -/
@[simp]
/-
**LinearMap.dualMap_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：dualMap_surjective_iff {f : V₁ ->ₗ[K] V₂} : Function.Surjective f.dualMap 
↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.range_dualMap_eq_dualAnnihilator_ker`：range_dualMap_eq_dualAnn
ihilator_ker (f : V₁ ->ₗ[K] V₂) : LinearMap.range f.dualMap = (LinearMap.ker f).
dualAnnihilator
· 使用定理 `Submodule.dualAnnihilator_bot`：dualAnnihilator_bot : (⊥ : Submodule R M)
.dualAnnihilator = ⊤
· 使用定理 `Subspace.dualAnnihilator_inj`：dualAnnihilator_inj {W W' : Subspace K V} 
: W.dualAnnihilator = W'.dualAnnihilator ↔ W = W'
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
For vector spaces, `f.dualMap` is surjective if and only if `f` is injective
-/
theorem dualMap_surjective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Surjective f.dualMap ↔ Function.Injective f := by
  rw [← LinearMap.range_eq_top, range_dualMap_eq_dualAnnihilator_ker,
      ← Submodule.dualAnnihilator_bot, Subspace.dualAnnihilator_inj, LinearMap.ker_eq_bot]

end LinearMap

variable {K V₁ V₂ : Type*} [Field K]
variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

namespace Subspace

open Submodule

/-
**Subspace.dualPairing_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualPairing_eq (W : Subspace K V₁) : W.dualPairing = W.quotAnnihilatorEqui
v.toLinearMap
参数：W : Subspace K V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.linearMap_qext`：linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h :
 f.comp p.mkQ = g.comp p.mkQ) : f = g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem dualPairing_eq (W : Subspace K V₁) :
    W.dualPairing = W.quotAnnihilatorEquiv.toLinearMap := by
  ext
  rfl
/-
**Subspace.dualPairing_nondegenerate** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualPairing_nondegenerate (W : Subspace K V₁) : W.dualPairing.Nondegenerat
e
参数：W : Subspace K V₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Subspace.dualPairing_eq`：dualPairing_eq (W : Subspace K V₁) : W.dualPair
ing = W.quotAnnihilatorEquiv.toLinearMap
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.forall_dual_apply_eq_zero_iff`：forall_dual_apply_eq_zero_iff (R :
 Type*) [Semiring R] [Module R V] [Projective R V] (v : V) : (forall φ : Module.
Dual R V, φ v = 0) ↔ v = 0
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subspace.dualLift_of_subtype`：dualLift_of_subtype {φ : Module.Dual K W} 
(w : W) : W.dualLift φ (w : V) = φ w
-/
theorem dualPairing_nondegenerate (W : Subspace K V₁) : W.dualPairing.Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualPairing_eq]
    apply LinearEquiv.ker
  · intro x h
    rw [← forall_dual_apply_eq_zero_iff K x]
    intro φ
    simpa only [Submodule.dualPairing_apply, dualLift_of_subtype] using
      h (Submodule.Quotient.mk (W.dualLift φ))
/-
**Subspace.dualCopairing_nondegenerate** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualCopairing_nondegenerate (W : Subspace K V₁) : W.dualCopairing.Nondegen
erate
参数：W : Subspace K V₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.dualCopairing_eq`：dualCopairing_eq (W : Submodule R M) : W.dua
lCopairing = (dualQuotEquivDualAnnihilator W).symm.toLinearMap
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`：forall_mem_dualAn
nihilator_apply_eq_zero_iff (W : Subspace K V) (v : V) : (forall φ : Module.Dual
 K V, φ in W.dualAnnihilator -> φ v = 0) ↔ …
· 使用定理 `SetLike.forall`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p : A
} {q : ↥p → Prop},   (∀ (x : ↥p), q x) ↔ ∀ (x : B) (h : x ∈ p), q ⟨x, h⟩
-/
theorem dualCopairing_nondegenerate (W : Subspace K V₁) : W.dualCopairing.Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualCopairing_eq]
    apply LinearEquiv.ker
  · rintro ⟨x⟩
    simp only [Quotient.quot_mk_eq_mk, dualCopairing_apply, Quotient.mk_eq_zero]
    rw [← forall_mem_dualAnnihilator_apply_eq_zero_iff, SetLike.forall]
    exact id

-- Argument from https://math.stackexchange.com/a/2423263/172988
/-
**Subspace.dualAnnihilator_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualAnnihilator_inf_eq (W W' : Subspace K V₁) : (W ⊓ W').dualAnnihilator =
 W.dualAnnihilator ⊔ W'.dualAnnihilator
参数：W W' : Subspace K V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_prod`：ker_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : ker (
prod f g) = ker f ⊓ ker g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_dualMap_eq_dualAnnihilator_ker`：range_dualMap_eq_dualAnn
ihilator_ker (f : V₁ ->ₗ[K] V₂) : LinearMap.range f.dualMap = (LinearMap.ker f).
dualAnnihilator
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.sup_dualAnnihilator_le_inf`：sup_dualAnnihilator_le_inf (U V : 
Submodule R M) : U.dualAnnihilator ⊔ V.dualAnnihilator <= (U ⊓ V).dualAnnihilato
r
-/
theorem dualAnnihilator_inf_eq (W W' : Subspace K V₁) :
    (W ⊓ W').dualAnnihilator = W.dualAnnihilator ⊔ W'.dualAnnihilator := by
  refine le_antisymm ?_ (sup_dualAnnihilator_le_inf W W')
  let F : V₁ →ₗ[K] (V₁ ⧸ W) × V₁ ⧸ W' := (Submodule.mkQ W).prod (Submodule.mkQ W')
  have : LinearMap.ker F = W ⊓ W' := by simp only [F, LinearMap.ker_prod, ker_mkQ]
  rw [← this, ← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  intro φ
  rw [LinearMap.mem_range]
  rintro ⟨x, rfl⟩
  rw [Submodule.mem_sup]
  obtain ⟨⟨a, b⟩, rfl⟩ := (dualProdDualEquivDual K (V₁ ⧸ W) (V₁ ⧸ W')).surjective x
  obtain ⟨a', rfl⟩ := (dualQuotEquivDualAnnihilator W).symm.surjective a
  obtain ⟨b', rfl⟩ := (dualQuotEquivDualAnnihilator W').symm.surjective b
  use a', a'.property, b', b'.property
  rfl

-- This is also true if `V₁` is finite dimensional since one can restrict `ι` to some subtype
-- for which the infimum and supremum are the same.
-- The obstruction to the `dualAnnihilator_inf_eq` argument carrying through is that we need
-- for `Module.Dual R (Π (i : ι), V ⧸ W i) ≃ₗ[K] Π (i : ι), Module.Dual R (V ⧸ W i)`, which is not
-- true for infinite `ι`. One would need to add additional hypothesis on `W` (for example, it might
-- be true when the family is inf-closed).
-- TODO: generalize to `Sort`
/-
**Subspace.dualAnnihilator_iInf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：dualAnnihilator_iInf_eq {ι : Type*} [Finite ι] (W : ι -> Subspace K V₁) : 
(⨅ i : ι, W i).dualAnnihilator = ⨆ i : ι, (W i).dualAnnihilator
参数：W : ι -> Subspace K V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.iInf_comp`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst :
 InfSet α] {g : ι' → α} (e : ι ≃ ι'), ⨅ x, g (e x) = ⨅ y, g y
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `iInf_of_isEmpty`：∀ {α : Type u_8} {ι : Sort u_9} [inst : InfSet α] [IsEm
pty ι] (f : ι → α), iInf f = sInf ∅
· 使用定理 `sInf_empty`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf ∅ = ⊤
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `Submodule.dualAnnihilator_top`：dualAnnihilator_top : (⊤ : Submodule R M)
.dualAnnihilator = ⊥
· 使用定理 `iInf_option`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
(f : Option β → α), ⨅ o, f o = f none ⊓ ⨅ b, f (some b)
· 使用定理 `iSup_option`：iSup_option (f : Option β -> α) : ⨆ o, f o = f none ⊔ ⨆ b, 
f (Option.some b)
· 使用定理 `Subspace.dualAnnihilator_inf_eq`：dualAnnihilator_inf_eq (W W' : Subspace
 K V₁) : (W ⊓ W').dualAnnihilator = W.dualAnnihilator ⊔ W'.dualAnnihilator
-/
theorem dualAnnihilator_iInf_eq {ι : Type*} [Finite ι] (W : ι → Subspace K V₁) :
    (⨅ i : ι, W i).dualAnnihilator = ⨆ i : ι, (W i).dualAnnihilator := by
  revert ι
  apply Finite.induction_empty_option
  · intro α β h hyp W
    rw [← h.iInf_comp, hyp _, ← h.iSup_comp]
  · intro W
    rw [iSup_of_empty', iInf_of_isEmpty, sInf_empty, sSup_empty, dualAnnihilator_top]
  · intro α _ h W
    rw [iInf_option, iSup_option, dualAnnihilator_inf_eq, h]

/-- For vector spaces, dual annihilators carry direct sum decompositions
to direct sum decompositions. -/
/-
**Subspace.isCompl_dualAnnihilator** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：isCompl_dualAnnihilator {W W' : Subspace K V₁} (h : IsCompl W W') : IsComp
l W.dualAnnihilator W'.dualAnnihilator
参数：h : IsCompl W W'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompl_iff`：isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} : I
sCompl a b ↔ Disjoint a b ∧ Codisjoint a b
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subspace.dualAnnihilator_inf_eq`：dualAnnihilator_inf_eq (W W' : Subspace
 K V₁) : (W ⊓ W').dualAnnihilator = W.dualAnnihilator ⊔ W'.dualAnnihilator
· 使用定理 `Submodule.dualAnnihilator_sup_eq`：dualAnnihilator_sup_eq (U V : Submodul
e R M) : (U ⊔ V).dualAnnihilator = U.dualAnnihilator ⊓ V.dualAnnihilator
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Submodule.dualAnnihilator_top`：dualAnnihilator_top : (⊤ : Submodule R M)
.dualAnnihilator = ⊥
· 使用定理 `Submodule.dualAnnihilator_bot`：dualAnnihilator_bot : (⊥ : Submodule R M)
.dualAnnihilator = ⊤

--- 原说明 ---
For vector spaces, dual annihilators carry direct sum decompositions
to direct sum decompositions.
-/
theorem isCompl_dualAnnihilator {W W' : Subspace K V₁} (h : IsCompl W W') :
    IsCompl W.dualAnnihilator W'.dualAnnihilator := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h ⊢
  rw [← dualAnnihilator_inf_eq, ← dualAnnihilator_sup_eq, h.1, h.2, dualAnnihilator_top,
    dualAnnihilator_bot]
  exact ⟨rfl, rfl⟩

/-- For finite-dimensional vector spaces, one can distribute duals over quotients by identifying
`W.dualLift.range` with `W`. Note that this depends on a choice of splitting of `V₁`. -/
/-
**Subspace.dualQuotDistrib** 是 Mathlib 中的一个定义，位于命名空间 `Subspace`。
形式化陈述：dualQuotDistrib [FiniteDimensional K V₁] (W : Subspace K V₁) : Module.Dual
 K (V₁ ⧸ W) ≃ₗ[K] Module.Dual K V₁ ⧸ LinearMap.range W.dualLift
参数：W : Subspace K V₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For finite-dimensional vector spaces, one can distribute duals over quotients by
 identifying
`W.dualLift.range` with `W`. Note that this depends on a choice of splitting of 
`V₁`.
-/
def dualQuotDistrib [FiniteDimensional K V₁] (W : Subspace K V₁) :
    Module.Dual K (V₁ ⧸ W) ≃ₗ[K] Module.Dual K V₁ ⧸ LinearMap.range W.dualLift :=
  W.dualQuotEquivDualAnnihilator.trans W.quotDualEquivAnnihilator.symm

end Subspace

section FiniteDimensional

open Module LinearMap

namespace LinearMap

@[simp]
/-
**LinearMap.finrank_range_dualMap_eq_finrank_range** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap`。
形式化陈述：finrank_range_dualMap_eq_finrank_range (f : V₁ ->ₗ[K] V₂) : finrank K (Lin
earMap.range f.dualMap) = finrank K (LinearMap.range f)
参数：f : V₁ ->ₗ[K] V₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.dualMap_comp_dualMap`：LinearMap.dualMap_comp_dualMap {M₃ : Typ
e*} [AddCommMonoid M₃] [Module R M₃] (f : M₁ ->ₗ[R] M₂) (g : M₂ ->ₗ[R] M₃) : f.d
ualMap.comp g.dualMa…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.dualMap_surjective_of_injective`：dualMap_surjective_of_injecti
ve {f : V₁ ->ₗ[K] V₂} (hf : Function.Injective f) : Function.Surjective f.dualMa
p
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.finrank_range_of_inj`：LinearMap.finrank_range_of_inj {f : M ->
ₗ[R] N} (hf : Function.Injective f) : finrank R (LinearMap.range f) = finrank R 
M
· 使用定理 `LinearMap.dualMap_injective_of_surjective`：LinearMap.dualMap_injective_o
f_surjective {f : M₁ ->ₗ[R] M₂} (hf : Function.Surjective f) : Function.Injectiv
e f.dualMap
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_rangeRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Typ
e u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Subspace.dual_finrank_eq`：dual_finrank_eq : finrank K (Module.Dual K V) 
= finrank K V
-/
theorem finrank_range_dualMap_eq_finrank_range (f : V₁ →ₗ[K] V₂) :
    finrank K (LinearMap.range f.dualMap) = finrank K (LinearMap.range f) := by
  rw [congr_arg dualMap (show f = (range f).subtype.comp f.rangeRestrict by rfl),
    ← dualMap_comp_dualMap, range_comp,
    range_eq_top.mpr (dualMap_surjective_of_injective (range f).injective_subtype),
    Submodule.map_top, finrank_range_of_inj, Subspace.dual_finrank_eq]
  exact dualMap_injective_of_surjective (range_eq_top.mp f.range_rangeRestrict)

/-- `f.dualMap` is injective if and only if `f` is surjective -/
@[simp]
/-
**LinearMap.dualMap_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：dualMap_injective_iff {f : V₁ ->ₗ[K] V₂} : Function.Injective f.dualMap ↔ 
Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Function.mtr`：∀ {a b : Prop}, (¬a → ¬b) → b → a
· 使用定理 `Submodule.exists_le_ker_of_lt_top`：Submodule.exists_le_ker_of_lt_top (p 
: Submodule K V) (hp : p < ⊤) : exists (f : V ->ₗ[K] K), f != 0 ∧ p <= ker f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.dualMap_injective_of_surjective`：LinearMap.dualMap_injective_o
f_surjective {f : M₁ ->ₗ[R] M₂} (hf : Function.Surjective f) : Function.Injectiv
e f.dualMap

--- 原说明 ---
`f.dualMap` is injective if and only if `f` is surjective
-/
theorem dualMap_injective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Injective f.dualMap ↔ Function.Surjective f := by
  refine ⟨Function.mtr fun not_surj inj ↦ ?_, dualMap_injective_of_surjective⟩
  rw [← range_eq_top, ← Ne, ← lt_top_iff_ne_top] at not_surj
  obtain ⟨φ, φ0, range_le_ker⟩ := (range f).exists_le_ker_of_lt_top not_surj
  exact φ0 (inj <| ext fun x ↦ range_le_ker ⟨x, rfl⟩)

/-- `f.dualMap` is bijective if and only if `f` is -/
@[simp]
/-
**LinearMap.dualMap_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：dualMap_bijective_iff {f : V₁ ->ₗ[K] V₂} : Function.Bijective f.dualMap ↔ 
Function.Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`f.dualMap` is bijective if and only if `f` is
-/
theorem dualMap_bijective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Bijective f.dualMap ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, dualMap_surjective_iff, dualMap_injective_iff, and_comm]

variable {B : V₁ →ₗ[K] V₂ →ₗ[K] K}

@[simp]
/-
**LinearMap.dualAnnihilator_ker_eq_range_flip** 是 Mathlib 中的一个引理，位于命名空间 `LinearM
ap`。
形式化陈述：dualAnnihilator_ker_eq_range_flip [IsReflexive K V₂] : (ker B).dualAnnihil
ator = range B.flip
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_dualMap_eq_dualAnnihilator_ker`：range_dualMap_eq_dualAnn
ihilator_ker (f : V₁ ->ₗ[K] V₂) : LinearMap.range f.dualMap = (LinearMap.ker f).
dualAnnihilator
· 使用定理 `LinearMap.range_comp_of_range_eq_top`：range_comp_of_range_eq_top [RingHo
mSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] {f : M ->ₛₗ[τ₁₂
] M₂} (g : M₂ ->ₛₗ[τ₂₃] M₃…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
-/
lemma dualAnnihilator_ker_eq_range_flip [IsReflexive K V₂] :
    (ker B).dualAnnihilator = range B.flip := by
  change _ = range (B.dualMap.comp (Module.evalEquiv K V₂).toLinearMap)
  rw [← range_dualMap_eq_dualAnnihilator_ker, range_comp_of_range_eq_top _ (LinearEquiv.range _)]

open Function
/-
**LinearMap.flip_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_injective_iff₁ [FiniteDimensional K V₁] : Injective B.flip ↔ Surjective B := by
  rw [← dualMap_surjective_iff, ← (evalEquiv K V₁).toEquiv.surjective_comp]; rfl
/-
**LinearMap.flip_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_injective_iff₂ [FiniteDimensional K V₂] : Injective B.flip ↔ Surjective B := by
  rw [← dualMap_injective_iff]; exact (evalEquiv K V₂).toEquiv.injective_comp B.dualMap
/-
**LinearMap.flip_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_surjective_iff₁ [FiniteDimensional K V₁] : Surjective B.flip ↔ Injective B :=
  flip_injective_iff₂.symm
/-
**LinearMap.flip_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_surjective_iff₂ [FiniteDimensional K V₂] : Surjective B.flip ↔ Injective B :=
  flip_injective_iff₁.symm
/-
**LinearMap.flip_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_bijective_iff₁ [FiniteDimensional K V₁] : Bijective B.flip ↔ Bijective B := by
  simp_rw [Bijective, flip_injective_iff₁, flip_surjective_iff₁, and_comm]
/-
**LinearMap.flip_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_bijective_iff₂ [FiniteDimensional K V₂] : Bijective B.flip ↔ Bijective B :=
  flip_bijective_iff₁.symm

end LinearMap

namespace Subspace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-
**Subspace.quotDualCoannihilatorToDual_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Subs
pace`。
形式化陈述：quotDualCoannihilatorToDual_bijective (W : Subspace K (Dual K V)) [FiniteD
imensional K W] : Function.Bijective W.quotDualCoannihilatorToDual
参数：W : Subspace K (Dual K V)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.quotDualCoannihilatorToDual_injective`：quotDualCoannihilatorTo
Dual_injective (W : Submodule R (Dual R M)) : Function.Injective W.quotDualCoann
ihilatorToDual
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.flip_injective_iff₂`：flip_injective_iff₂ [FiniteDimensional K 
V₂] : Injective B.flip ↔ Surjective B
· 使用定理 `Submodule.flip_quotDualCoannihilatorToDual_injective`：flip_quotDualCoann
ihilatorToDual_injective (W : Submodule R (Dual R M)) : Function.Injective W.quo
tDualCoannihilatorToDual.flip
-/
theorem quotDualCoannihilatorToDual_bijective (W : Subspace K (Dual K V)) [FiniteDimensional K W] :
    Function.Bijective W.quotDualCoannihilatorToDual :=
  ⟨W.quotDualCoannihilatorToDual_injective, letI : AddCommGroup W := inferInstance
    flip_injective_iff₂.mp W.flip_quotDualCoannihilatorToDual_injective⟩
/-
**Subspace.flip_quotDualCoannihilatorToDual_bijective** 是 Mathlib 中的一个定理，位于命名空间 
`Subspace`。
形式化陈述：flip_quotDualCoannihilatorToDual_bijective (W : Subspace K (Dual K V)) [Fi
niteDimensional K W] : Function.Bijective W.quotDualCoannihilatorToDual.flip
参数：W : Subspace K (Dual K V)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.flip_bijective_iff₂`：flip_bijective_iff₂ [FiniteDimensional K 
V₂] : Bijective B.flip ↔ Bijective B
· 使用定理 `Subspace.quotDualCoannihilatorToDual_bijective`：quotDualCoannihilatorToD
ual_bijective (W : Subspace K (Dual K V)) [FiniteDimensional K W] : Function.Bij
ective W.quotDualCoannihilatorToDual
-/
theorem flip_quotDualCoannihilatorToDual_bijective (W : Subspace K (Dual K V))
    [FiniteDimensional K W] : Function.Bijective W.quotDualCoannihilatorToDual.flip :=
  letI : AddCommGroup W := inferInstance
  flip_bijective_iff₂.mpr W.quotDualCoannihilatorToDual_bijective
/-
**Subspace.dualCoannihilator_dualAnnihilator_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subsp
ace`。
形式化陈述：dualCoannihilator_dualAnnihilator_eq {W : Subspace K (Dual K V)} [FiniteDi
mensional K W] : W.dualCoannihilator.dualAnnihilator = W
参数：Dual K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Subspace.flip_quotDualCoannihilatorToDual_bijective`：flip_quotDualCoanni
hilatorToDual_bijective (W : Subspace K (Dual K V)) [FiniteDimensional K W] : Fu
nction.Bijective W.quotDualCoannihilatorT…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
· 使用定理 `Submodule.le_dualCoannihilator_dualAnnihilator`：le_dualCoannihilator_dua
lAnnihilator (U : Submodule R (Module.Dual R M)) : U <= U.dualCoannihilator.dual
Annihilator
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
theorem dualCoannihilator_dualAnnihilator_eq {W : Subspace K (Dual K V)} [FiniteDimensional K W] :
    W.dualCoannihilator.dualAnnihilator = W :=
  let e := (LinearEquiv.ofBijective _ W.flip_quotDualCoannihilatorToDual_bijective).trans
    (Submodule.dualQuotEquivDualAnnihilator _)
  letI : AddCommGroup W := inferInstance
  haveI : FiniteDimensional K W.dualCoannihilator.dualAnnihilator := LinearEquiv.finiteDimensional e
  (eq_of_le_of_finrank_eq W.le_dualCoannihilator_dualAnnihilator e.finrank_eq).symm
/-
**Subspace.finiteDimensional_quot_dualCoannihilator_iff** 是 Mathlib 中的一个定理，位于命名空
间 `Subspace`。
形式化陈述：finiteDimensional_quot_dualCoannihilator_iff {W : Submodule K (Dual K V)} 
: FiniteDimensional K (V ⧸ W.dualCoannihilator) ↔ FiniteDimensional K W
参数：Dual K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `FiniteDimensional.of_injective`：of_injective (f : V ->ₗ[K] V₂) (w : Func
tion.Injective f) [FiniteDimensional K V₂] : FiniteDimensional K V
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Submodule.flip_quotDualCoannihilatorToDual_injective`：flip_quotDualCoann
ihilatorToDual_injective (W : Submodule R (Dual R M)) : Function.Injective W.quo
tDualCoannihilatorToDual.flip
· 使用定理 `Submodule.quotDualCoannihilatorToDual_injective`：quotDualCoannihilatorTo
Dual_injective (W : Submodule R (Dual R M)) : Function.Injective W.quotDualCoann
ihilatorToDual
-/
theorem finiteDimensional_quot_dualCoannihilator_iff {W : Submodule K (Dual K V)} :
    FiniteDimensional K (V ⧸ W.dualCoannihilator) ↔ FiniteDimensional K W :=
  ⟨fun _ ↦ FiniteDimensional.of_injective _ W.flip_quotDualCoannihilatorToDual_injective,
    fun _ ↦ FiniteDimensional.of_injective _ W.quotDualCoannihilatorToDual_injective⟩

open OrderDual in
/-- For any vector space, `dualAnnihilator` and `dualCoannihilator` gives an antitone order
  isomorphism between the finite-codimensional subspaces in the vector space and the
  finite-dimensional subspaces in its dual. -/
/-
**Subspace.orderIsoFiniteCodimDim** 是 Mathlib 中的一个定义，位于命名空间 `Subspace`。
形式化陈述：orderIsoFiniteCodimDim : {W : Subspace K V // FiniteDimensional K (V ⧸ W)}
 ≃o {W : Subspace K (Dual K V) // FiniteDimensional K W}ᵒᵈ where toFun W
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any vector space, `dualAnnihilator` and `dualCoannihilator` gives an antiton
e order
  isomorphism between the finite-codimensional subspaces in the vector space and
 the
  finite-dimensional subspaces in its dual.
-/
def orderIsoFiniteCodimDim :
    {W : Subspace K V // FiniteDimensional K (V ⧸ W)} ≃o
    {W : Subspace K (Dual K V) // FiniteDimensional K W}ᵒᵈ where
  toFun W := toDual ⟨W.1.dualAnnihilator, Submodule.finite_dualAnnihilator_iff.mpr W.2⟩
  invFun W := ⟨(ofDual W).1.dualCoannihilator,
    finiteDimensional_quot_dualCoannihilator_iff.mpr (ofDual W).2⟩
  left_inv _ := Subtype.ext dualAnnihilator_dualCoannihilator_eq
  right_inv W := have := (ofDual W).2; Subtype.ext dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

open OrderDual in
/-- For any finite-dimensional vector space, `dualAnnihilator` and `dualCoannihilator` give
  an antitone order isomorphism between the subspaces in the vector space and the subspaces
  in its dual. -/
/-
**Subspace.orderIsoFiniteDimensional** 是 Mathlib 中的一个定义，位于命名空间 `Subspace`。
形式化陈述：orderIsoFiniteDimensional [FiniteDimensional K V] : Subspace K V ≃o (Subsp
ace K (Dual K V))ᵒᵈ where toFun W
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subspace.dualAnnihilator_dualCoannihilator_eq`：dualAnnihilator_dualCoann
ihilator_eq {W : Subspace K V} : W.dualAnnihilator.dualCoannihilator = W
· 使用定理 `Subspace.dualAnnihilator_le_dualAnnihilator_iff`：dualAnnihilator_le_dual
Annihilator_iff {W W' : Subspace K V} : W.dualAnnihilator <= W'.dualAnnihilator 
↔ W' <= W

--- 原说明 ---
For any finite-dimensional vector space, `dualAnnihilator` and `dualCoannihilato
r` give
  an antitone order isomorphism between the subspaces in the vector space and th
e subspaces
  in its dual.
-/
def orderIsoFiniteDimensional [FiniteDimensional K V] :
    Subspace K V ≃o (Subspace K (Dual K V))ᵒᵈ where
  toFun W := toDual W.dualAnnihilator
  invFun W := (ofDual W).dualCoannihilator
  left_inv _ := dualAnnihilator_dualCoannihilator_eq
  right_inv _ := dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

open Submodule in
/-
**Subspace.dualAnnihilator_dualAnnihilator_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Sub
space`。
形式化陈述：dualAnnihilator_dualAnnihilator_eq_map (W : Subspace K V) [FiniteDimension
al K W] : W.dualAnnihilator.dualAnnihilator = W.map (Dual.eval K V)
参数：W : Subspace K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.finiteDimensional`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {V₂ : Type v
'} [inst_3 : AddCom…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_of_le_of_finrank_eq`：eq_of_le_of_finrank_eq {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₁ = finrank 
K S₂) : S₁ = S₂
· 使用定理 `Subspace.map_le_dualAnnihilator_dualAnnihilator`：map_le_dualAnnihilator_
dualAnnihilator (W : Subspace K V) : W.map (Module.Dual.eval K V) <= W.dualAnnih
ilator.dualAnnihilator
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Module.eval_apply_injective`：eval_apply_injective : Function.Injective (
eval K V)
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
-/
theorem dualAnnihilator_dualAnnihilator_eq_map (W : Subspace K V) [FiniteDimensional K W] :
    W.dualAnnihilator.dualAnnihilator = W.map (Dual.eval K V) := by
  let e1 := (Free.chooseBasis K W).toDualEquiv ≪≫ₗ W.quotAnnihilatorEquiv.symm
  have := e1.finiteDimensional
  let e2 := (Free.chooseBasis K _).toDualEquiv ≪≫ₗ W.dualAnnihilator.dualQuotEquivDualAnnihilator
  have := LinearEquiv.finiteDimensional (V₂ := W.dualAnnihilator.dualAnnihilator) e2
  rw [eq_of_le_of_finrank_eq (map_le_dualAnnihilator_dualAnnihilator W)]
  rw [← (equivMapOfInjective _ (eval_apply_injective K (V := V)) W).finrank_eq, e1.finrank_eq]
  exact e2.finrank_eq
/-
**Subspace.map_dualCoannihilator** 是 Mathlib 中的一个定理，位于命名空间 `Subspace`。
形式化陈述：map_dualCoannihilator (W : Subspace K (Dual K V)) [FiniteDimensional K V] 
: W.dualCoannihilator.map (Dual.eval K V) = W.dualAnnihilator
参数：W : Subspace K (Dual K V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subspace.dualAnnihilator_dualAnnihilator_eq_map`：dualAnnihilator_dualAnn
ihilator_eq_map (W : Subspace K V) [FiniteDimensional K W] : W.dualAnnihilator.d
ualAnnihilator = W.map (Dual.eval K V…
· 使用定理 `Subspace.dualCoannihilator_dualAnnihilator_eq`：dualCoannihilator_dualAnn
ihilator_eq {W : Subspace K (Dual K V)} [FiniteDimensional K W] : W.dualCoannihi
lator.dualAnnihilator = W
-/
theorem map_dualCoannihilator (W : Subspace K (Dual K V)) [FiniteDimensional K V] :
    W.dualCoannihilator.map (Dual.eval K V) = W.dualAnnihilator := by
  rw [← dualAnnihilator_dualAnnihilator_eq_map, dualCoannihilator_dualAnnihilator_eq]

end Subspace

end FiniteDimensional

end VectorSpace

/-
**span_flip_eq_top_iff_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：span_flip_eq_top_iff_linearIndependent {ι α F} [Finite ι] [Field F] {f : ι
 -> α -> F} : span F (Set.range <| flip f) = ⊤ ↔ LinearIndependent F f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff_ker`：linearIndependent_iff_ker : LinearIndependent
 R v ↔ LinearMap.ker (Finsupp.linearCombination R v) = ⊥
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_eq_top_iff`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Subspace.dualCoannihilator_dualAnnihilator_eq`：dualCoannihilator_dualAnn
ihilator_eq {W : Subspace K (Dual K V)} [FiniteDimensional K W] : W.dualCoannihi
lator.dualAnnihilator = W
· 使用定理 `FiniteDimensional.instSubtypeMemSubmoduleMap`：∀ (K : Type u) {V : Type v
} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]
   {V₂ : Type v'} [inst_3 : AddCom…
· 使用定理 `Submodule.dualAnnihilator_eq_top_iff`：∀ {R : Type u_1} {M : Type u_2} [i
nst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {W : 
Submodule R M} [Module.Pro…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用引理 `Submodule.coe_dualCoannihilator_span`：coe_dualCoannihilator_span (s : Se
t (Module.Dual R M)) : ((span R s).dualCoannihilator : Set M) = {x | forall f in
 s, f x = 0}
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem span_flip_eq_top_iff_linearIndependent {ι α F} [Finite ι] [Field F] {f : ι → α → F} :
    span F (Set.range <| flip f) = ⊤ ↔ LinearIndependent F f := by
  rw [linearIndependent_iff_ker, ← Submodule.map_eq_top_iff (e := Finsupp.llift F F F ι),
    ← Subspace.dualCoannihilator_dualAnnihilator_eq (W := map ..), dualAnnihilator_eq_top_iff]
  congr!
  rw [SetLike.ext'_iff, map_span, Submodule.coe_dualCoannihilator_span, ← Set.range_comp]
  ext
  simp [funext_iff, Finsupp.linearCombination, Finsupp.sum, Finset.sum_apply, flip]
/-
**Module.exists_dual_forall_apply_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.exists_dual_forall_apply_eq_one {ι K V : Type*} [Field K] [AddCommG
roup V] [Module K V] {s : Set ι} {v : ι -> V} (hli : LinearIndepOn K v s) : exis
ts f : Dual K V, forall i in s, f (v i) = 1
参数：hli : LinearIndepOn K v s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.id_image`：LinearIndepOn.id_image (hs : LinearIndepOn R v s
) : LinearIndepOn R id (v '' s)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `LinearIndepOn.linearIndepOn_extend`：LinearIndepOn.linearIndepOn_extend (
hs : LinearIndepOn K v s) (hst : s subseteq t) : LinearIndepOn K v (hs.extend hs
t)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Submodule.span_univ`：span_univ : span R (univ : Set M) = ⊤
· 使用定理 `LinearIndepOn.span_extend_eq_span`：LinearIndepOn.span_extend_eq_span {s 
t : Set V} (hs : LinearIndepOn K id s) (hst : s subseteq t) : span K (hs.extend 
hst) = span K t
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearIndepOn.subset_extend`：LinearIndepOn.subset_extend (hs : LinearInd
epOn K v s) (hst : s subseteq t) : s subseteq hs.extend hst
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
-/
lemma Module.exists_dual_forall_apply_eq_one {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {s : Set ι} {v : ι → V} (hli : LinearIndepOn K v s) :
    ∃ f : Dual K V, ∀ i ∈ s, f (v i) = 1 := by
  replace hli : LinearIndepOn K id (v '' s) := LinearIndepOn.id_image hli
  let b : Basis _ K V := .mk (hli.linearIndepOn_extend (Set.subset_univ _)) <| by
    simpa using hli.span_extend_eq_span <| Set.subset_univ _
  refine ⟨b.constr K 1, fun i hi ↦ ?_⟩
  replace hi : v i ∈ hli.extend (Set.subset_univ _) :=
    hli.subset_extend _ <| Set.mem_image_of_mem v hi
  let ri : hli.extend (Set.subset_univ _) := ⟨v i, hi⟩
  have : b ri = v i := by simp [b, ri]
  simp [← this]

namespace TensorProduct

variable (R A : Type*) (M : Type*) (N : Type*)
variable {ι κ : Type*}
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι] [Fintype κ]

open TensorProduct

attribute [local ext] TensorProduct.ext

open TensorProduct

open LinearMap

section

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- The canonical linear map from `Dual M ⊗ Dual N` to `Dual (M ⊗ N)`,
sending `f ⊗ g` to the composition of `TensorProduct.map f g` with
the natural isomorphism `R ⊗ R ≃ R`.
-/
/-
**TensorProduct.dualDistrib** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：dualDistrib : Dual R M otimes[R] Dual R N ->ₗ[R] Dual R (M otimes[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map from `Dual M ⊗ Dual N` to `Dual (M ⊗ N)`,
sending `f ⊗ g` to the composition of `TensorProduct.map f g` with
the natural isomorphism `R ⊗ R ≃ R`.
-/
def dualDistrib : Dual R M ⊗[R] Dual R N →ₗ[R] Dual R (M ⊗[R] N) :=
  compRight _ (TensorProduct.lid R R) ∘ₗ homTensorHomMap (.id R) M N R R

variable {R M N}

@[simp]
/-
**TensorProduct.dualDistrib_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：dualDistrib_apply (f : Dual R M) (g : Dual R N) (m : M) (n : N) : dualDist
rib R M N (f otimesₜ g) (m otimesₜ n) = f m * g n
参数：f : Dual R M；g : Dual R N；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualDistrib_apply (f : Dual R M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R M N (f ⊗ₜ g) (m ⊗ₜ n) = f m * g n :=
  rfl

/-- Simultaneously swapping both the ordering of the applied duals and the ordering of the
tensor product argument preserves evaluation. -/
/-
**TensorProduct.dualDistrib_apply_comm** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`
。
形式化陈述：dualDistrib_apply_comm (w : Dual R N otimes[R] Dual R M) (z : M otimes[R] 
N) : dualDistrib R N M w (TensorProduct.comm R M N z) = dualDistrib R M N (Tenso
rProduct.comm R _ _ w) z
参数：w : Dual R N otimes[R] Dual R M；z : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
Simultaneously swapping both the ordering of the applied duals and the ordering 
of the
tensor product argument preserves evaluation.
-/
lemma dualDistrib_apply_comm (w : Dual R N ⊗[R] Dual R M) (z : M ⊗[R] N) :
    dualDistrib R N M w (TensorProduct.comm R M N z) =
      dualDistrib R M N (TensorProduct.comm R _ _ w) z := by
  induction w <;> induction z <;> simp_all [mul_comm]

end

namespace AlgebraTensorModule
variable [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module A M] [Module R N] [IsScalarTower R A M]

/-- Heterobasic version of `TensorProduct.dualDistrib` -/
/-
**TensorProduct.AlgebraTensorModule.dualDistrib** 是 Mathlib 中的一个定义，位于命名空间 `Tenso
rProduct.AlgebraTensorModule`。
形式化陈述：dualDistrib : Dual A M otimes[R] Dual R N ->ₗ[A] Dual A (M otimes[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Heterobasic version of `TensorProduct.dualDistrib`
-/
def dualDistrib : Dual A M ⊗[R] Dual R N →ₗ[A] Dual A (M ⊗[R] N) :=
  compRight _ (Algebra.TensorProduct.rid R A A).toLinearMap ∘ₗ homTensorHomMap R A A M N A R

variable {R M N}

@[simp]
/-
**TensorProduct.AlgebraTensorModule.dualDistrib_apply** 是 Mathlib 中的一个定理，位于命名空间 
`TensorProduct.AlgebraTensorModule`。
形式化陈述：dualDistrib_apply (f : Dual A M) (g : Dual R N) (m : M) (n : N) : dualDist
rib R A M N (f otimesₜ g) (m otimesₜ n) = g n • f m
参数：f : Dual A M；g : Dual R N；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem dualDistrib_apply (f : Dual A M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R A M N (f ⊗ₜ g) (m ⊗ₜ n) = g n • f m :=
  rfl

end AlgebraTensorModule

end TensorProduct

