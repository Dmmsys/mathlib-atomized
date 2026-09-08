/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Data.SubtypeNeLift
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Generators of multiple tensor products

Given a finite family of `R`-modules `M i`, if we have, for each `i`,
a family of generators of the module `M i`, then the tensor products
of these elements generate `⨂[R] i, M i`.

In `LinearAlgebra.PiTensorProduct.Finite`, we deduce that if the modules `M i`
are finitely generated, then so is `⨂[R] i, M i`.

-/

@[expose] public section

open TensorProduct

namespace PiTensorProduct

variable (R : Type*)

section equivPiTensorComplSingletonTensor

variable {ι : Type*} [DecidableEq ι] (M : ι → Type*)
  [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The linear equivalence between `⨂[R] i, M i` and the tensor product of
the pi tensor product indexed by the complement of `{i₀}` and `M i₀`. -/
/-
**PiTensorProduct.equivPiTensorComplSingletonTensor** 是 Mathlib 中的一个定义，位于命名空间 `P
iTensorProduct`。
形式化陈述：equivPiTensorComplSingletonTensor (i₀ : ι) : (⨂[R] i, M i) ≃ₗ[R] ((⨂[R] (i
 : ({i₀}ᶜ : Set ι)), M i) otimes[R] M i₀)
参数：i₀ : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}

--- 原说明 ---
The linear equivalence between `⨂[R] i, M i` and the tensor product of
the pi tensor product indexed by the complement of `{i₀}` and `M i₀`.
-/
noncomputable def equivPiTensorComplSingletonTensor (i₀ : ι) :
    (⨂[R] i, M i) ≃ₗ[R] ((⨂[R] (i : ({i₀}ᶜ : Set ι)), M i) ⊗[R] M i₀) :=
  (reindex R (s := M) (Equiv.subtypeNeSumPUnit.{0} i₀).symm).trans
    ((tmulEquivDep R (fun i ↦ M (Equiv.subtypeNeSumPUnit i₀ i))).symm.trans
      (LinearEquiv.lTensor _ (subsingletonEquiv Unit.unit)))

variable (i₀ : ι)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PiTensorProduct.equivPiTensorComplSingletonTensor_tprod** 是 Mathlib 中的一个引理，位于命
名空间 `PiTensorProduct`。
形式化陈述：equivPiTensorComplSingletonTensor_tprod (i₀ : ι) (m : forall i, M i) : equ
ivPiTensorComplSingletonTensor R M i₀ (⨂ₜ[R] i, m i) = (⨂ₜ[R] (j : ((Set.singlet
on i₀)ᶜ : Set ι)), m j) otimesₜ m i₀
参数：i₀ : ι；m : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.reindex_tprod`：reindex_tprod (e : ι ≃ ι₂) (f : Π i, s i)
 : reindex R s e (tprod R f) = tprod R fun i => f (e.symm i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `PiTensorProduct.tmulEquivDep_symm_apply`：tmulEquivDep_symm_apply (f : (i
 : ι oplus ι₂) -> N i) : (tmulEquivDep R N).symm (⨂ₜ[R] i, f i) = ((⨂ₜ[R] i₁, f 
(.inl i₁)) otimesₜ (⨂ₜ[R] i₂,…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.lTensor_tmul`：∀ {R : Type u_1} [inst : CommSemiring R] (M : 
Type u_7) {N : Type u_8} {P : Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : A
ddCommMonoid N…
· 使用定理 `PiTensorProduct.subsingletonEquiv_apply_tprod`：subsingletonEquiv_apply_t
prod (f : (i : ι) -> s i) : subsingletonEquiv i₀ (⨂ₜ[R] i, f i) = f i₀
-/
lemma equivPiTensorComplSingletonTensor_tprod (i₀ : ι) (m : ∀ i, M i) :
    equivPiTensorComplSingletonTensor R M i₀ (⨂ₜ[R] i, m i) =
      (⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j) ⊗ₜ m i₀:= by
  dsimp [equivPiTensorComplSingletonTensor]
  have : (reindex R M (Equiv.subtypeNeSumPUnit.{0} i₀).symm) (⨂ₜ[R] (i : ι), m i) =
      ⨂ₜ[R] j, m ((Equiv.subtypeNeSumPUnit.{0} i₀) j) := by
    simp_rw [reindex_tprod (R := R) (s := M), Equiv.symm_symm]
  rw [dsimp% this, dsimp% tmulEquivDep_symm_apply R
    (fun i ↦ M ((Equiv.subtypeNeSumPUnit.{0} i₀) i))]
  exact (LinearEquiv.lTensor_tmul _ _ _ _).trans (by congr; simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**PiTensorProduct.equivPiTensorComplSingletonTensor_symm_tmul** 是 Mathlib 中的一个引理
，位于命名空间 `PiTensorProduct`。
形式化陈述：equivPiTensorComplSingletonTensor_symm_tmul (i₀ : ι) (m : forall (i : ((Se
t.singleton i₀)ᶜ : Set ι)), M i) (x : M i₀) : (equivPiTensorComplSingletonTensor
 R M i₀).symm ((⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j) otimesₜ x) = (⨂ₜ
[R] i, Function.subtypeNeLift i₀ m x i)
参数：i₀ : ι；m : forall (i : ((Set.singleton i₀)ᶜ : Set ι)), M i；x : M i₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PiTensorProduct.equivPiTensorComplSingletonTensor_tprod`：equivPiTensorCo
mplSingletonTensor_tprod (i₀ : ι) (m : forall i, M i) : equivPiTensorComplSingle
tonTensor R M i₀ (⨂ₜ[R] i, m i) = (⨂ₜ[R] (j :…
· 使用引理 `Function.subtypeNeLift_self`：subtypeNeLift_self : subtypeNeLift i₀ f x i
₀ = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Function.subtypeNeLift_of_neq`：subtypeNeLift_of_neq (i : ι) (h : i != i₀
) : subtypeNeLift i₀ f x i = f ⟨i, h⟩
-/
lemma equivPiTensorComplSingletonTensor_symm_tmul (i₀ : ι)
    (m : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) (x : M i₀) :
    (equivPiTensorComplSingletonTensor R M i₀).symm
      ((⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j) ⊗ₜ x) =
    (⨂ₜ[R] i, Function.subtypeNeLift i₀ m x i) := by
  apply (equivPiTensorComplSingletonTensor R M i₀).injective
  simp only [LinearEquiv.apply_symm_apply, equivPiTensorComplSingletonTensor_tprod,
    Function.subtypeNeLift_self]
  congr
  ext ⟨i, hi⟩
  rw [Function.subtypeNeLift_of_neq _ _ _ _ hi]
  rfl

end equivPiTensorComplSingletonTensor

variable {R} {ι : Type*} [Finite ι] {M : ι → Type*} {N : Type*} {γ : ι → Type*}

section AddCommMonoid

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid N] [Module R N] {g : ⦃i : ι⦄ → (j : γ i) → M i}

set_option backward.isDefEq.respectTransparency.types false in
/-
**PiTensorProduct.ext_of_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProduct`
。
形式化陈述：ext_of_span_eq_top (hg : forall i, Submodule.span R (Set.range (@g i)) = ⊤
) {φ φ' : (⨂[R] i, M i) ->ₗ[R] N} (h : forall (j : (i : ι) -> γ i), φ (tprod _ (
fun i => g (j i))) = φ' (tprod _ (fun i => g (j i)))) : φ = φ'
参数：hg : forall i, Submodule.span R (Set.range (@g i)) = ⊤；⨂[R] i, M i；h : forall
 (j : (i : ι) -> γ i), φ (tprod _ (fun i => g (j i))) = φ' (tprod _ (fun i => g 
(j i)))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.card_eq_zero`：card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α
· 使用定理 `Finite.not_infinite`：∀ {α : Sort u_1}, Finite α → ¬Infinite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Nat.card_pos_iff`：card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `Submodule.linearMap_eq_iff_of_span_eq_top`：linearMap_eq_iff_of_span_eq_t
op (f g : M ->ₗ[R] N) {S : Set M} (hM : span R S = ⊤) : f = g ↔ forall (s : S), 
f s = g s
· 使用引理 `PiTensorProduct.equivPiTensorComplSingletonTensor_tprod`：equivPiTensorCo
mplSingletonTensor_tprod (i₀ : ι) (m : forall i, M i) : equivPiTensorComplSingle
tonTensor R M i₀ (⨂ₜ[R] i, m i) = (⨂ₜ[R] (j :…
· 使用引理 `Function.subtypeNeLift_self`：subtypeNeLift_self : subtypeNeLift i₀ f x i
₀ = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Function.subtypeNeLift_of_neq`：subtypeNeLift_of_neq (i : ι) (h : i != i₀
) : subtypeNeLift i₀ f x i = f ⟨i, h⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.ncard_compl_of_ncard_eq_add`：ncard_compl_of_ncard_eq_add [Finite α] 
(s : Set α) {n : Nat} (h : Nat.card α = n + s.ncard) : sᶜ.ncard = n
· 使用定理 `Set.ncard_singleton`：∀ {α : Type u_1} (a : α), {a}.ncard = 1
-/
lemma ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : (⨂[R] i, M i) →ₗ[R] N}
    (h : ∀ (j : (i : ι) → γ i),
      φ (tprod _ (fun i ↦ g (j i))) = φ' (tprod _ (fun i ↦ g (j i)))) :
    φ = φ' := by
  obtain ⟨n, hι⟩ : ∃ (n : ℕ), Nat.card ι = n := ⟨_, rfl⟩
  induction n generalizing ι with
  | zero =>
    ext x
    have : IsEmpty ι := (Nat.card_eq_zero.1 hι).resolve_right <| Finite.not_infinite ‹_›
    obtain rfl : x = fun i ↦ @g i (isEmptyElim i) := Subsingleton.elim _ _
    apply h
  | succ n hn =>
    classical
    have : Nonempty ι := ((Nat.card_pos_iff (α := ι)).1 (by omega)).1
    have i₀ : ι := Classical.arbitrary _
    let e := (equivPiTensorComplSingletonTensor R M i₀).trans (TensorProduct.comm _ _ _)
    obtain ⟨ψ, rfl⟩ : ∃ ψ, φ = LinearMap.comp ψ e.toLinearMap :=
      ⟨φ.comp e.symm.toLinearMap, by ext; simp⟩
    obtain ⟨ψ', rfl⟩ : ∃ ψ', φ' = LinearMap.comp ψ' e.toLinearMap :=
      ⟨φ'.comp e.symm.toLinearMap, by ext; simp⟩
    dsimp [e] at h
    congr 1
    apply (TensorProduct.lift.equiv _ _ _ _).symm.injective
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (hg i₀)]
    rintro ⟨_, ⟨g₀, rfl⟩⟩
    apply hn (g := fun i (j : γ i.1) ↦ by exact g j)
    · intro
      exact hg _
    · intro j
      have : (g g₀ ⊗ₜ[R] (tprod R) fun i ↦ g (j i)) =
          TensorProduct.comm R _ _ ((equivPiTensorComplSingletonTensor R M i₀)
            (⨂ₜ[R] (i : ι), g (Function.subtypeNeLift i₀ j g₀ i))) := by
        simp only [equivPiTensorComplSingletonTensor_tprod, Function.subtypeNeLift_self]
        congr
        ext ⟨x, hx⟩
        congr
        rw [Function.subtypeNeLift_of_neq _ _ _ _ (by assumption)]
        rfl
      simpa only [lift.equiv_symm_apply, this] using h (Function.subtypeNeLift i₀ j g₀)
    · exact Set.ncard_compl_of_ncard_eq_add _ (by simpa)
/-
**PiTensorProduct._root_.MultilinearMap.ext_of_span_eq_top** 是 Mathlib 中的一个引理，位于
命名空间 `PiTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MultilinearMap.ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : MultilinearMap R M N}
    (h : ∀ (j : (i : ι) → γ i), φ (fun i ↦ g (j i)) = φ' (fun i ↦ g (j i))) :
    φ = φ' := by
  suffices lift φ = lift φ' by
    ext m
    simpa using DFunLike.congr_fun this (tprod _ m)
  exact PiTensorProduct.ext_of_span_eq_top hg (fun j ↦ by simpa using h j)

end AddCommMonoid

variable [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid N] [Module R N] {g : ⦃i : ι⦄ → (j : γ i) → M i}

/-
**PiTensorProduct.submodule_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProdu
ct`。
形式化陈述：submodule_span_eq_top (hg : forall i, Submodule.span R (Set.range (@g i)) 
= ⊤) : Submodule.span R (Set.range (fun j : ((i : ι) -> γ i) => ⨂ₜ[R] (i : ι), g
 (j i))) = ⊤
参数：hg : forall i, Submodule.span R (Set.range (@g i)) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `LinearMap.ker_eq_top`：ker_eq_top {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 
0
· 使用引理 `PiTensorProduct.ext_of_span_eq_top`：ext_of_span_eq_top (hg : forall i, S
ubmodule.span R (Set.range (@g i)) = ⊤) {φ φ' : (⨂[R] i, M i) ->ₗ[R] N} (h : for
all (j : (i : ι) -> γ i)…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
lemma submodule_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤) :
    Submodule.span R (Set.range (fun j : ((i : ι) → γ i) ↦
      ⨂ₜ[R] (i : ι), g (j i))) = ⊤ := by
  rw [← (Submodule.span R _).ker_mkQ, LinearMap.ker_eq_top]
  refine ext_of_span_eq_top hg (fun j ↦ ?_)
  simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨j, rfl⟩

end PiTensorProduct

