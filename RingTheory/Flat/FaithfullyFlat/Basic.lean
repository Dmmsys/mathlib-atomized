/-
Copyright (c) 2024 Judith Ludwig, Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Florent Schaffhauser, Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Flat.Stability

/-!
# Faithfully flat modules

A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and `IM ≠ M` whenever
`I` is a maximal ideal of `R`.

## Main declaration

- `Module.FaithfullyFlat`: the predicate asserting that an `R`-module `M` is faithfully flat.

## Main theorems

- `Module.FaithfullyFlat.iff_flat_and_proper_ideal`: an `R`-module `M` is faithfully flat iff it is
  flat and for all proper ideals `I` of `R`, `I • M ≠ M`.
- `Module.FaithfullyFlat.iff_flat_and_rTensor_faithful`: an `R`-module `M` is faithfully flat iff it
  is flat and tensoring with `M` is faithful, i.e. `N ≠ 0` implies `N ⊗ M ≠ 0`.
- `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful`: an `R`-module `M` is faithfully flat iff it
  is flat and tensoring with `M` is faithful, i.e. `N ≠ 0` implies `M ⊗ N ≠ 0`.
- `Module.FaithfullyFlat.iff_exact_iff_rTensor_exact`: an `R`-module `M` is faithfully flat iff
  tensoring with `M` preserves and reflects exact sequences, i.e. the sequence `N₁ → N₂ → N₃` is
  exact *iff* the sequence `N₁ ⊗ M → N₂ ⊗ M → N₃ ⊗ M` is exact.
- `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`: an `R`-module `M` is faithfully flat iff
  tensoring with `M` preserves and reflects exact sequences, i.e. the sequence `N₁ → N₂ → N₃` is
  exact *iff* the sequence `M ⊗ N₁ → M ⊗ N₂ → M ⊗ N₃` is exact.
- `Module.FaithfullyFlat.iff_zero_iff_lTensor_zero`: an `R`-module `M` is faithfully flat iff for
  all linear maps `f : N → N'`, `f = 0` iff `M ⊗ f = 0`.
- `Module.FaithfullyFlat.iff_zero_iff_rTensor_zero`: an `R`-module `M` is faithfully flat iff for
  all linear maps `f : N → N'`, `f = 0` iff `f ⊗ M = 0`.

- `Module.FaithfullyFlat.of_linearEquiv`: modules linearly equivalent to a flat modules are flat
- `Module.FaithfullyFlat.trans`: if `S` is `R`-faithfully flat and `M` is `S`-faithfully flat, then
  `M` is `R`-faithfully flat.

- `Module.FaithfullyFlat.self`: the `R`-module `R` is faithfully flat.

-/

@[expose] public section

universe u v

open TensorProduct DirectSum

namespace Module

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/--
A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and,
for all `R`-linear maps `f : N → N'` such that `id ⊗ f = 0`, we have `f = 0`.
-/
/-
**Module.FaithfullyFlat** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u) → (M : Type v) → [inst : CommRing R] → [inst_1 : AddCommGroup
 M] → [_root_.Module R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and,
for all `R`-linear maps `f : N → N'` such that `id ⊗ f = 0`, we have `f = 0`.
-/
@[mk_iff] class FaithfullyFlat : Prop extends Module.Flat R M where
  submodule_ne_top : ∀ ⦃m : Ideal R⦄ (_ : Ideal.IsMaximal m), m • (⊤ : Submodule R M) ≠ ⊤

namespace FaithfullyFlat
/-
**Module.FaithfullyFlat.self** 是 Mathlib 中的一个实例，位于命名空间 `Module.FaithfullyFlat`。
形式化陈述：self : FaithfullyFlat R R where .not.1 h.ne_top by submodule_ne_top m h r
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance self : FaithfullyFlat R R where
  submodule_ne_top m h r := Ideal.eq_top_iff_one _ |>.not.1 h.ne_top <| by
    simpa using show 1 ∈ (m • ⊤ : Ideal R) from r.symm ▸ ⟨⟩

section proper_ideal

/-
**Module.FaithfullyFlat.iff_flat_and_proper_ideal** 是 Mathlib 中的一个引理，位于命名空间 `Mod
ule.FaithfullyFlat`。
形式化陈述：iff_flat_and_proper_ideal : FaithfullyFlat R M ↔ (Flat R M ∧ forall (I : I
deal R), I != ⊤ -> I • (⊤ : Submodule R M) != ⊤)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.faithfullyFlat_iff`：∀ (R : Type u) (M : Type v) [inst : CommRing 
R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   Module.FaithfullyFl
at R M ↔ Module…
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submodule.smul_mono`：smul_mono (hij : I <= J) (hnp : N <= P) : I • N <= 
J • P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
-/
lemma iff_flat_and_proper_ideal :
    FaithfullyFlat R M ↔
    (Flat R M ∧ ∀ (I : Ideal R), I ≠ ⊤ → I • (⊤ : Submodule R M) ≠ ⊤) := by
  rw [faithfullyFlat_iff]
  refine ⟨fun ⟨flat, h⟩ => ⟨flat, fun I hI r => ?_⟩, fun h => ⟨h.1, fun m hm => h.2 _ hm.ne_top⟩⟩
  obtain ⟨m, hm, le⟩ := I.exists_le_maximal hI
  exact h hm <| eq_top_iff.2 <| show ⊤ ≤ m • ⊤ from r ▸ Submodule.smul_mono le (by simp [r])
/-
**Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top** 是 Mathlib 中的一个引理，位于命名空间
 `Module.FaithfullyFlat`。
形式化陈述：iff_flat_and_ideal_smul_eq_top : FaithfullyFlat R M ↔ (Flat R M ∧ forall (
I : Ideal R), I • (⊤ : Submodule R M) = ⊤ -> I = ⊤)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Module.FaithfullyFlat.iff_flat_and_proper_ideal`：iff_flat_and_proper_ide
al : FaithfullyFlat R M ↔ (Flat R M ∧ forall (I : Ideal R), I != ⊤ -> I • (⊤ : S
ubmodule R M) != ⊤)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
lemma iff_flat_and_ideal_smul_eq_top :
    FaithfullyFlat R M ↔
    (Flat R M ∧ ∀ (I : Ideal R), I • (⊤ : Submodule R M) = ⊤ → I = ⊤) :=
  iff_flat_and_proper_ideal R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun I => eq_iff_iff.2 <| by tauto

end proper_ideal

section faithful

/-
**Module.FaithfullyFlat.rTensor_nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Module.Fai
thfullyFlat`。
形式化陈述：rTensor_nontrivial [fl : FaithfullyFlat R M] (N : Type*) [AddCommGroup N] 
[Module R N] [Nontrivial N] : Nontrivial (N otimes[R] M)
参数：N : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nontrivial_iff_exists_ne`：nontrivial_iff_exists_ne (x : α) : Nontrivial 
α ↔ exists y, y != x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submodule.mem_annihilator_span_singleton`：mem_annihilator_span_singleton
 (g : M) (r : R) : r in (Submodule.span R ({g} : Set M)).annihilator ↔ r • g = 0
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Module.FaithfullyFlat.iff_flat_and_proper_ideal`：iff_flat_and_proper_ide
al : FaithfullyFlat R M ↔ (Flat R M ∧ forall (I : Ideal R), I != ⊤ -> I • (⊤ : S
ubmodule R M) != ⊤)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.Quotient.subsingleton_iff`：∀ {R : Type u_1} {M : Type u_2} [in
st : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submo
dule R M}, Subsingleton (…
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
instance rTensor_nontrivial
    [fl : FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Nontrivial N] :
    Nontrivial (N ⊗[R] M) := by
  obtain ⟨n, hn⟩ := nontrivial_iff_exists_ne (0 : N) |>.1 inferInstance
  let I := (Submodule.span R {n}).annihilator
  by_cases I_ne_top : I = ⊤
  · rw [Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul] at I_ne_top
    contradiction
  let inc : R ⧸ I →ₗ[R] N := Submodule.liftQ _ ((LinearMap.lsmul R N).flip n) <| fun r hr => by
    simpa only [LinearMap.mem_ker, LinearMap.flip_apply, LinearMap.lsmul_apply,
      Submodule.mem_annihilator_span_singleton, I] using hr
  have injective_inc : Function.Injective inc := LinearMap.ker_eq_bot.1 <| eq_bot_iff.2 <| by
    intro r hr
    induction r using Quotient.inductionOn' with | h r =>
    simpa only [Submodule.Quotient.mk''_eq_mk, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_annihilator_span_singleton, LinearMap.mem_ker, Submodule.liftQ_apply,
      LinearMap.flip_apply, LinearMap.lsmul_apply, I, inc] using hr
  have ne_top := iff_flat_and_proper_ideal R M |>.1 fl |>.2 I I_ne_top
  refine subsingleton_or_nontrivial _ |>.resolve_left fun rid => ne_top ?_
  rw [← Submodule.Quotient.subsingleton_iff]
  exact (fl.toFlat.rTensor_preserves_injective_linearMap inc injective_inc).comp
    (quotTensorEquivQuotSMul M I).symm.injective |>.subsingleton
/-
**Module.FaithfullyFlat.lTensor_nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Module.Fai
thfullyFlat`。
形式化陈述：lTensor_nontrivial [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Modu
le R N] [Nontrivial N] : Nontrivial (M otimes[R] N)
参数：N : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
-/
instance lTensor_nontrivial
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Nontrivial N] :
    Nontrivial (M ⊗[R] N) :=
  TensorProduct.comm R M N |>.toEquiv.nontrivial
/-
**Module.FaithfullyFlat.rTensor_reflects_triviality** 是 Mathlib 中的一个引理，位于命名空间 `M
odule.FaithfullyFlat`。
形式化陈述：rTensor_reflects_triviality [FaithfullyFlat R M] (N : Type*) [AddCommGroup
 N] [Module R N] [h : Subsingleton (N otimes[R] M)] : Subsingleton N
参数：N : Type*；N otimes[R] M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma rTensor_reflects_triviality
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N]
    [h : Subsingleton (N ⊗[R] M)] : Subsingleton N := by
  revert h; change _ → _; contrapose!
  intro h
  infer_instance
/-
**Module.FaithfullyFlat.lTensor_reflects_triviality** 是 Mathlib 中的一个引理，位于命名空间 `M
odule.FaithfullyFlat`。
形式化陈述：lTensor_reflects_triviality [FaithfullyFlat R M] (N : Type*) [AddCommGroup
 N] [Module R N] [Subsingleton (M otimes[R] N)] : Subsingleton N
参数：N : Type*；M otimes[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用引理 `Module.FaithfullyFlat.rTensor_reflects_triviality`：rTensor_reflects_triv
iality [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [h : Subsi
ngleton (N otimes[R] M)] : Subsingleton…
-/
lemma lTensor_reflects_triviality
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N]
    [Subsingleton (M ⊗[R] N)] :
    Subsingleton N := by
  have : Subsingleton (N ⊗[R] M) := (TensorProduct.comm R N M).toEquiv.injective.subsingleton
  apply rTensor_reflects_triviality R M

attribute [-simp] Ideal.Quotient.mk_eq_mk in
/-
**Module.FaithfullyFlat.iff_flat_and_rTensor_faithful** 是 Mathlib 中的一个引理，位于命名空间 
`Module.FaithfullyFlat`。
形式化陈述：iff_flat_and_rTensor_faithful : FaithfullyFlat R M ↔ (Flat R M ∧ forall (N
 : Type max u v) [AddCommGroup N] [Module R N], Nontrivial N -> Nontrivial (N ot
imes[R] M))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.Quotient.subsingleton_iff`：∀ {R : Type u_1} {M : Type u_2} [in
st : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submo
dule R M}, Subsingleton (…
-/
lemma iff_flat_and_rTensor_faithful :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Nontrivial N → Nontrivial (N ⊗[R] M)) := by
  refine ⟨fun fl => ⟨inferInstance, rTensor_nontrivial R M⟩, fun ⟨flat, faithful⟩ => ⟨?_⟩⟩
  intro m hm rid
  specialize faithful (ULift (R ⧸ m)) inferInstance
  have : Nontrivial ((R ⧸ m) ⊗[R] M) :=
    (congr (ULift.moduleEquiv : ULift (R ⧸ m) ≃ₗ[R] R ⧸ m)
      (LinearEquiv.refl R M)).symm.toEquiv.nontrivial
  have := (quotTensorEquivQuotSMul M m).toEquiv.symm.nontrivial
  refine not_subsingleton (M ⧸ m • (⊤ : Submodule R M)) ?_
  rwa [Submodule.Quotient.subsingleton_iff]
/-
**Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality** 是 Mathlib 中的一
个引理，位于命名空间 `Module.FaithfullyFlat`。
形式化陈述：iff_flat_and_rTensor_reflects_triviality : FaithfullyFlat R M ↔ (Flat R M 
∧ forall (N : Type max u v) [AddCommGroup N] [Module R N], Subsingleton (N otime
s[R] M) -> Subsingleton N)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Module.FaithfullyFlat.iff_flat_and_rTensor_faithful`：iff_flat_and_rTenso
r_faithful : FaithfullyFlat R M ↔ (Flat R M ∧ forall (N : Type max u v) [AddComm
Group N] [Module R N], Nontrivial N -> No…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
lemma iff_flat_and_rTensor_reflects_triviality :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Subsingleton (N ⊗[R] M) → Subsingleton N) :=
  iff_flat_and_rTensor_faithful R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 <| by
      simp only [← not_subsingleton_iff_nontrivial]; tauto
/-
**Module.FaithfullyFlat.iff_flat_and_lTensor_faithful** 是 Mathlib 中的一个引理，位于命名空间 
`Module.FaithfullyFlat`。
形式化陈述：iff_flat_and_lTensor_faithful : FaithfullyFlat R M ↔ (Flat R M ∧ forall (N
 : Type max u v) [AddCommGroup N] [Module R N], Nontrivial N -> Nontrivial (M ot
imes[R] N))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Module.FaithfullyFlat.iff_flat_and_rTensor_faithful`：iff_flat_and_rTenso
r_faithful : FaithfullyFlat R M ↔ (Flat R M ∧ forall (N : Type max u v) [AddComm
Group N] [Module R N], Nontrivial N -> No…
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
-/
lemma iff_flat_and_lTensor_faithful :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Nontrivial N → Nontrivial (M ⊗[R] N)) :=
  iff_flat_and_rTensor_faithful R M |>.trans
  ⟨fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).toEquiv.nontrivial⟩,
    fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).symm.toEquiv.nontrivial⟩⟩
/-
**Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality** 是 Mathlib 中的一
个引理，位于命名空间 `Module.FaithfullyFlat`。
形式化陈述：iff_flat_and_lTensor_reflects_triviality : FaithfullyFlat R M ↔ (Flat R M 
∧ forall (N : Type max u v) [AddCommGroup N] [Module R N], Subsingleton (M otime
s[R] N) -> Subsingleton N)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful`：iff_flat_and_lTenso
r_faithful : FaithfullyFlat R M ↔ (Flat R M ∧ forall (N : Type max u v) [AddComm
Group N] [Module R N], Nontrivial N -> No…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
lemma iff_flat_and_lTensor_reflects_triviality :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Subsingleton (M ⊗[R] N) → Subsingleton N) :=
  iff_flat_and_lTensor_faithful R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 <| by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

end faithful

/-- If `M` is a faithfully flat `R`-module and `N` is `R`-linearly isomorphic to `M`, then
`N` is faithfully flat. -/
/-
**Module.FaithfullyFlat.of_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Module.Faithfu
llyFlat`。
形式化陈述：of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] [FaithfullyFlat R
 M] (e : N ≃ₗ[R] M) : FaithfullyFlat R N
参数：e : N ≃ₗ[R] M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful`：iff_flat_and_lTenso
r_faithful : FaithfullyFlat R M ↔ (Flat R M ∧ forall (N : Type max u v) [AddComm
Group N] [Module R N], Nontrivial N -> No…
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α

--- 原说明 ---
If `M` is a faithfully flat `R`-module and `N` is `R`-linearly isomorphic to `M`
, then
`N` is faithfully flat.
-/
lemma of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] [FaithfullyFlat R M]
    (e : N ≃ₗ[R] M) : FaithfullyFlat R N := by
  rw [iff_flat_and_lTensor_faithful]
  exact ⟨Flat.of_linearEquiv e,
    fun P _ _ hP ↦ (TensorProduct.congr e (LinearEquiv.refl R P)).toEquiv.nontrivial⟩

section

/-- A direct sum of faithfully flat `R`-modules is faithfully flat. -/
/-
**Module.FaithfullyFlat.directSum** 是 Mathlib 中的一个实例，位于命名空间 `Module.FaithfullyFl
at`。
形式化陈述：directSum {ι : Type*} [Nonempty ι] (M : ι -> Type*) [forall i, AddCommGrou
p (M i)] [forall i, Module R (M i)] [forall i, FaithfullyFlat R (M i)] : Faithfu
llyFlat R (⨁ i, M i)
参数：M : ι -> Type*；M i；M i；M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful`：iff_flat_and_lTenso
r_faithful : FaithfullyFlat R M ↔ (Flat R M ∧ forall (N : Type max u v) [AddComm
Group N] [Module R N], Nontrivial N -> No…
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用定理 `DirectSum.of_injective`：of_injective (i : ι) : Function.Injective (of β 
i)
· 使用定理 `Equiv.nontrivial`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) [Nontrivia
l β], Nontrivial α
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
A direct sum of faithfully flat `R`-modules is faithfully flat.
-/
instance directSum {ι : Type*} [Nonempty ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [∀ i, FaithfullyFlat R (M i)] : FaithfullyFlat R (⨁ i, M i) := by
  classical
  rw [iff_flat_and_lTensor_faithful]
  refine ⟨inferInstance, fun N _ _ hN ↦ ?_⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨x, y, hxy⟩ := Nontrivial.exists_pair_ne (α := M i ⊗[R] N)
  have : Nontrivial (⨁ (i : ι), M i ⊗[R] N) :=
    ⟨DirectSum.of _ i x, DirectSum.of _ i y, fun h ↦ hxy (DirectSum.of_injective i h)⟩
  apply (TensorProduct.directSumLeft R R M N).toEquiv.nontrivial

/-- Free `R`-modules over discrete types are flat. -/
/-
**Module.FaithfullyFlat.finsupp** 是 Mathlib 中的一个实例，位于命名空间 `Module.FaithfullyFlat
`。
形式化陈述：finsupp (ι : Type v) [Nonempty ι] : FaithfullyFlat R (ι ->₀ R)
参数：ι : Type v。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.FaithfullyFlat.of_linearEquiv`：of_linearEquiv {N : Type*} [AddCom
mGroup N] [Module R N] [FaithfullyFlat R M] (e : N ≃ₗ[R] M) : FaithfullyFlat R N

--- 原说明 ---
Free `R`-modules over discrete types are flat.
-/
instance finsupp (ι : Type v) [Nonempty ι] : FaithfullyFlat R (ι →₀ R) := by
  classical exact of_linearEquiv _ _ (finsuppLEquivDirectSum R R ι)

end

/-- Any free, nontrivial `R`-module is flat. -/
/-
**Module.FaithfullyFlat.** 是 Mathlib 中的一个实例，位于命名空间 `Module.FaithfullyFlat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any free, nontrivial `R`-module is flat.
-/
instance [Nontrivial M] [Module.Free R M] : FaithfullyFlat R M :=
  of_linearEquiv _ _ (Free.chooseBasis R M).repr

section

variable {N : Type*} [AddCommGroup N] [Module R N]

@[simp]
/-
**Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right** 是 Mathlib 中的一个引理，
位于命名空间 `Module.FaithfullyFlat`。
形式化陈述：subsingleton_tensorProduct_iff_right [Module.FaithfullyFlat R M] : Subsing
leton (M otimes[R] N) ↔ Subsingleton N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.FaithfullyFlat.lTensor_reflects_triviality`：lTensor_reflects_triv
iality [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Subsingle
ton (M otimes[R] N)] : Subsingleton N
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma subsingleton_tensorProduct_iff_right [Module.FaithfullyFlat R M] :
    Subsingleton (M ⊗[R] N) ↔ Subsingleton N :=
  ⟨fun _ ↦ lTensor_reflects_triviality R M N, fun _ ↦ inferInstance⟩

@[simp]
/-
**Module.FaithfullyFlat.subsingleton_tensorProduct_iff_left** 是 Mathlib 中的一个引理，位
于命名空间 `Module.FaithfullyFlat`。
形式化陈述：subsingleton_tensorProduct_iff_left [Module.FaithfullyFlat R N] : Subsingl
eton (M otimes[R] N) ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.FaithfullyFlat.rTensor_reflects_triviality`：rTensor_reflects_triv
iality [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [h : Subsi
ngleton (N otimes[R] M)] : Subsingleton…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma subsingleton_tensorProduct_iff_left [Module.FaithfullyFlat R N] :
    Subsingleton (M ⊗[R] N) ↔ Subsingleton M :=
  ⟨fun _ ↦ rTensor_reflects_triviality R N M, fun _ ↦ inferInstance⟩

@[simp]
/-
**Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right** 是 Mathlib 中的一个引理，位于
命名空间 `Module.FaithfullyFlat`。
形式化陈述：nontrivial_tensorProduct_iff_right [Module.FaithfullyFlat R M] : Nontrivia
l (M otimes[R] N) ↔ Nontrivial N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right`：subsingleton
_tensorProduct_iff_right [Module.FaithfullyFlat R M] : Subsingleton (M otimes[R]
 N) ↔ Subsingleton N
-/
lemma nontrivial_tensorProduct_iff_right [Module.FaithfullyFlat R M] :
    Nontrivial (M ⊗[R] N) ↔ Nontrivial N := by
  contrapose!; exact subsingleton_tensorProduct_iff_right R M

@[simp]
/-
**Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left** 是 Mathlib 中的一个引理，位于命
名空间 `Module.FaithfullyFlat`。
形式化陈述：nontrivial_tensorProduct_iff_left [Module.FaithfullyFlat R N] : Nontrivial
 (M otimes[R] N) ↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.FaithfullyFlat.subsingleton_tensorProduct_iff_left`：subsingleton_
tensorProduct_iff_left [Module.FaithfullyFlat R N] : Subsingleton (M otimes[R] N
) ↔ Subsingleton M
-/
lemma nontrivial_tensorProduct_iff_left [Module.FaithfullyFlat R N] :
    Nontrivial (M ⊗[R] N) ↔ Nontrivial M := by
  contrapose!; exact subsingleton_tensorProduct_iff_left R M

end

section exact

/-!
### Faithfully flat modules and exact sequences

In this section we prove that an `R`-module `M` is faithfully flat iff tensoring with `M`
preserves and reflects exact sequences.

Let `N₁ -l₁₂-> N₂ -l₂₃-> N₃` be two linear maps.
- We first show that if `N₁ ⊗ M -> N₂ ⊗ M -> N₃ ⊗ M` is exact, then `N₁ -l₁₂-> N₂ -l₂₃-> N₃` is a
  complex, i.e. `range l₁₂ ≤ ker l₂₃`.
  This is `range_le_ker_of_exact_rTensor`.
- Then in `rTensor_reflects_exact`, we show `ker l₂₃ = range l₁₂` by considering the cohomology
  `ker l₂₃ ⧸ range l₁₂`.

This shows that when `M` is faithfully flat, `- ⊗ M` reflects exact sequences. For details, see
comments in the proof. Since `M` is flat, `- ⊗ M` preserves exact sequences.

On the other hand, if `- ⊗ M` preserves and reflects exact sequences, then `M` is faithfully flat.
- `M` is flat because `- ⊗ M` preserves exact sequences.
- We need to show that if `N ⊗ M = 0` then `N = 0`. Consider the sequence `N -0-> N -0-> 0`. After
  tensoring with `M`, we get `N ⊗ M -0-> N ⊗ M -0-> 0` which is exact because `N ⊗ M = 0`.
  Since `- ⊗ M` reflects exact sequences, `N = 0`.
-/

section arbitrary_universe

variable {N1 : Type*} [AddCommGroup N1] [Module R N1]
variable {N2 : Type*} [AddCommGroup N2] [Module R N2]
variable {N3 : Type*} [AddCommGroup N3] [Module R N3]
variable (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3)

/--
If `M` is faithfully flat, then exactness of `N₁ ⊗ M -> N₂ ⊗ M -> N₃ ⊗ M` implies that the
composition `N₁ -> N₂ -> N₃` is `0`.

Implementation detail, please use `rTensor_reflects_exact` instead.
-/
/-
**Module.FaithfullyFlat.range_le_ker_of_exact_rTensor** 是 Mathlib 中的一个引理，位于命名空间 
`Module.FaithfullyFlat`。
形式化陈述：range_le_ker_of_exact_rTensor [fl : FaithfullyFlat R M] (ex : Function.Exa
ct (l12.rTensor M) (l23.rTensor M)) : LinearMap.range l12 <= LinearMap.ker l23
参数：ex : Function.Exact (l12.rTensor M) (l23.rTensor M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Function.Exact.apply_apply_eq_zero`：∀ {M : Type u_2} {N : Type u_4} {P :
 Type u_6} {f : M → N} {g : N → P} [inst : Zero P],   Function.Exact f g → ∀ (x 
: M), g (f x) = 0
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Submodule.mem_span_set`：Submodule.mem_span_set {m : M} {s : Set M} : m i
n Submodule.span R s ↔ exists c : M ->₀ R, (c.support : Set M) subseteq s ∧ (c.s
um fun mi r …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.span_tmul_eq_top`：span_tmul_eq_top : Submodule.span R { t 
: M otimes[R] N | exists m n, m otimesₜ n = t } = ⊤
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.rTensor_tmul`：rTensor_tmul (m : M) (n : N) : f.rTensor M (n ot
imesₜ m) = f n otimesₜ m
· 使用定理 `Submodule.subtype_apply`：subtype_apply (x : p) : p.subtype x = x
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If `M` is faithfully flat, then exactness of `N₁ ⊗ M -> N₂ ⊗ M -> N₃ ⊗ M` implie
s that the
composition `N₁ -> N₂ -> N₃` is `0`.

Implementation detail, please use `rTensor_reflects_exact` instead.
-/
lemma range_le_ker_of_exact_rTensor [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
    LinearMap.range l12 ≤ LinearMap.ker l23 := by
  -- let `n1 ∈ N1`. We need to show `l23 (l12 n1) = 0`. Suppose this is not the case.
  rintro _ ⟨n1, rfl⟩
  rw [LinearMap.mem_ker]
  by_contra! hn1
  -- Let `E` be the submodule spanned by `l23 (l12 n1)`. Then because `l23 (l12 n1) ≠ 0`, we have
  -- `E ≠ 0`.
  let E : Submodule R N3 := Submodule.span R {l23 (l12 n1)}
  have hE : Nontrivial E :=
    ⟨0, ⟨⟨l23 (l12 n1), Submodule.mem_span_singleton_self _⟩, Subtype.coe_ne_coe.1 hn1.symm⟩⟩
  -- Since `N1 ⊗ M -> N2 ⊗ M -> N3 ⊗ M` is exact, we have `l23 (l12 n1) ⊗ₜ m = 0` for all `m : M`.
  have eq1 : ∀ (m : M), l23 (l12 n1) ⊗ₜ[R] m = 0 := fun m ↦
    ex.apply_apply_eq_zero (n1 ⊗ₜ[R] m)
  -- Then `E ⊗ M = 0`. Indeed,
  have eq0 : (⊤ : Submodule R (E ⊗[R] M)) = ⊥ := by
    -- suppose `x ∈ E ⊗ M`. We will show `x = 0`.
    ext x
    simp only [Submodule.mem_top, Submodule.mem_bot, true_iff]
    have mem : x ∈ (⊤ : Submodule R _) := ⟨⟩
    rw [← TensorProduct.span_tmul_eq_top, Submodule.mem_span_set] at mem
    obtain ⟨c, hc, rfl⟩ := mem
    choose b a hy using hc
    let r : ⦃a : E ⊗[R] M⦄ → a ∈ ↑c.support → R := fun a ha =>
      Submodule.mem_span_singleton.1 (b ha).2 |>.choose
    have hr : ∀ ⦃i : E ⊗[R] M⦄ (hi : i ∈ c.support), b hi =
        r hi • ⟨l23 (l12 n1), Submodule.mem_span_singleton_self _⟩ := fun a ha =>
      Subtype.ext <| Submodule.mem_span_singleton.1 (b ha).2 |>.choose_spec.symm
    -- Since `M` is flat and `E -> N1` is injective, we only need to check that x = 0
    -- in `N1 ⊗ M`. We write `x = ∑ μᵢ • (l23 (l12 n1)) ⊗ mᵢ = ∑ μᵢ • 0 = 0`
    -- (remember `E = span {l23 (l12 n1)}` and `eq1`)
    refine Finset.sum_eq_zero fun i hi => show c i • i = 0 from
      (Module.Flat.rTensor_preserves_injective_linearMap (M := M) E.subtype <|
              Submodule.injective_subtype E) ?_
    rw [← hy hi, hr hi, smul_tmul, map_smul, LinearMap.rTensor_tmul, Submodule.subtype_apply, eq1,
      smul_zero, map_zero]
  have : Subsingleton (E ⊗[R] M) := subsingleton_iff_forall_eq 0 |>.2 fun x =>
    show x ∈ (⊥ : Submodule R _) from eq0 ▸ ⟨⟩
  -- but `E ⊗ M = 0` implies `E = 0` because `M` is faithfully flat and this is a contradiction.
  exact not_subsingleton_iff_nontrivial.2 inferInstance <| fl.rTensor_reflects_triviality R M E
/-
**Module.FaithfullyFlat.rTensor_reflects_exact** 是 Mathlib 中的一个引理，位于命名空间 `Module
.FaithfullyFlat`。
形式化陈述：rTensor_reflects_exact [fl : FaithfullyFlat R M] (ex : Function.Exact (l12
.rTensor M) (l23.rTensor M)) : Function.Exact l12 l23
参数：ex : Function.Exact (l12.rTensor M) (l23.rTensor M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用引理 `Module.FaithfullyFlat.range_le_ker_of_exact_rTensor`：range_le_ker_of_exa
ct_rTensor [fl : FaithfullyFlat R M] (ex : Function.Exact (l12.rTensor M) (l23.r
Tensor M)) : LinearMap.range l12 <= Linea…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `Submodule.Quotient.subsingleton_iff`：∀ {R : Type u_1} {M : Type u_2} [in
st : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p : Submo
dule R M}, Subsingleton (…
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.rTensor_def`：rTensor_def : f.rTensor M = TensorProduct.map f L
inearMap.id
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearMap.subtype_comp_codRestrict`：subtype_comp_codRestrict (p : Submod
ule R₂ M₂) (h : forall b, f b in p) : p.subtype.comp (codRestrict p f h) = f
· 使用定理 `Submodule.subtype_comp_inclusion`：subtype_comp_inclusion (p q : Submodul
e R M) (h : p <= q) : q.subtype.comp (inclusion h) = p.subtype
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
（共 35 条，此处仅展示前 30 条）
-/
lemma rTensor_reflects_exact [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
    Function.Exact l12 l23 := LinearMap.exact_iff.2 <| by
  have complex : LinearMap.range l12 ≤ LinearMap.ker l23 := range_le_ker_of_exact_rTensor R M _ _ ex
  -- By the previous lemma we have that range l12 ≤ ker l23 and hence the quotient
  -- H := ker l23 ⧸ range l12 makes sense.
  -- Hence our goal ker l23 = range l12 follows from the claim that H = 0.
  let H := LinearMap.ker l23 ⧸ LinearMap.range (Submodule.inclusion complex)
  suffices triv_coh : Subsingleton H by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.range_inclusion,
      Submodule.comap_subtype_eq_top] at triv_coh
    exact le_antisymm triv_coh complex
  -- Since `M` is faithfully flat, we need only to show that `H ⊗ M` is trivial.
  suffices Subsingleton (H ⊗[R] M) from rTensor_reflects_triviality R M H
  let e : H ⊗[R] M ≃ₗ[R] _ := TensorProduct.quotientTensorEquiv _ _
  -- Note that `H ⊗ M` is isomorphic to `ker l12 ⊗ M ⧸ range ((range l12 ⊗ M) -> (ker l23 ⊗ M))`.
  -- So the problem is reduced to proving surjectivity of `range l12 ⊗ M → ker l23 ⊗ M`.
  rw [e.toEquiv.subsingleton_congr, Submodule.Quotient.subsingleton_iff,
    LinearMap.range_eq_top]
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  -- let `x ⊗ m` be an element in `ker l23 ⊗ M`, then `x ⊗ m` is in the kernel of `l23 ⊗ 𝟙M`.
  -- Since `N1 ⊗ M -l12 ⊗ M-> N2 ⊗ M -l23 ⊗ M-> N3 ⊗ M` is exact, we have that `x ⊗ m` is in
  -- the range of `l12 ⊗ 𝟙M`, i.e. `x ⊗ m = (l12 ⊗ 𝟙M) y` for some `y ∈ N1 ⊗ M` as elements of
  -- `N2 ⊗ M`. We need to prove that `x ⊗ m = (l12 ⊗ 𝟙M) y` still holds in `(ker l23) ⊗ M`.
  -- This is okay because `M` is flat and `ker l23 -> N2` is injective.
  | tmul x m =>
    rcases x with ⟨x, (hx : l23 x = 0)⟩
    have mem : x ⊗ₜ[R] m ∈ LinearMap.ker (l23.rTensor M) := by simp [hx]
    rw [LinearMap.exact_iff.1 ex] at mem
    obtain ⟨y, hy⟩ := mem
    refine ⟨LinearMap.rTensor M (LinearMap.rangeRestrict _ ∘ₗ LinearMap.rangeRestrict l12) y,
      Module.Flat.rTensor_preserves_injective_linearMap (LinearMap.ker l23).subtype
      Subtype.val_injective ?_⟩
    simp only [LinearMap.comp_codRestrict, LinearMap.rTensor_tmul, Submodule.coe_subtype, ← hy]
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_def, ← LinearMap.rTensor_comp,
      ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, LinearMap.comp_assoc,
      LinearMap.subtype_comp_codRestrict, ← LinearMap.comp_assoc, Submodule.subtype_comp_inclusion,
      LinearMap.subtype_comp_codRestrict]
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, by simp⟩
/-
**Module.FaithfullyFlat.lTensor_reflects_exact** 是 Mathlib 中的一个引理，位于命名空间 `Module
.FaithfullyFlat`。
形式化陈述：lTensor_reflects_exact [fl : FaithfullyFlat R M] (ex : Function.Exact (l12
.lTensor M) (l23.lTensor M)) : Function.Exact l12 l23
参数：ex : Function.Exact (l12.lTensor M) (l23.lTensor M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.FaithfullyFlat.rTensor_reflects_exact`：rTensor_reflects_exact [fl
 : FaithfullyFlat R M] (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) : F
unction.Exact l12 l23
· 使用引理 `Function.Exact.of_ladder_linearEquiv_of_exact`：of_ladder_linearEquiv_of_
exact (h₁₂ : g₁₂ ∘ₗ e₁ = e₂ ∘ₗ f₁₂) (h₂₃ : g₂₃ ∘ₗ e₂ = e₃ ∘ₗ f₂₃) (H : Exact f₁₂
 f₂₃) : Exact g₁₂ g₂₃
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma lTensor_reflects_exact [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.lTensor M) (l23.lTensor M)) :
    Function.Exact l12 l23 :=
  rTensor_reflects_exact R M _ _ <| ex.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.comm _ _ _) (e₂ := TensorProduct.comm _ _ _)
    (e₃ := TensorProduct.comm _ _ _) (by ext; rfl) (by ext; rfl)

@[simp]
/-
**Module.FaithfullyFlat.rTensor_exact_iff_exact** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e.FaithfullyFlat`。
形式化陈述：rTensor_exact_iff_exact [FaithfullyFlat R M] : Function.Exact (l12.rTensor
 M) (l23.rTensor M) ↔ Function.Exact l12 l23
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.FaithfullyFlat.rTensor_reflects_exact`：rTensor_reflects_exact [fl
 : FaithfullyFlat R M] (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) : F
unction.Exact l12 l23
· 使用引理 `Module.Flat.rTensor_exact`：rTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [
AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] 
[Module R N''] …
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
-/
lemma rTensor_exact_iff_exact [FaithfullyFlat R M] :
    Function.Exact (l12.rTensor M) (l23.rTensor M) ↔ Function.Exact l12 l23 :=
  ⟨fun ex ↦ rTensor_reflects_exact R M l12 l23 ex, fun e ↦ Module.Flat.rTensor_exact _ e⟩

@[simp]
/-
**Module.FaithfullyFlat.lTensor_exact_iff_exact** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e.FaithfullyFlat`。
形式化陈述：lTensor_exact_iff_exact [FaithfullyFlat R M] : Function.Exact (l12.lTensor
 M) (l23.lTensor M) ↔ Function.Exact l12 l23
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.FaithfullyFlat.lTensor_reflects_exact`：lTensor_reflects_exact [fl
 : FaithfullyFlat R M] (ex : Function.Exact (l12.lTensor M) (l23.lTensor M)) : F
unction.Exact l12 l23
· 使用引理 `Module.Flat.lTensor_exact`：lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [
AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] 
[Module R N''] …
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
-/
lemma lTensor_exact_iff_exact [FaithfullyFlat R M] :
    Function.Exact (l12.lTensor M) (l23.lTensor M) ↔ Function.Exact l12 l23 :=
  ⟨fun ex ↦ lTensor_reflects_exact R M l12 l23 ex, fun e ↦ Module.Flat.lTensor_exact _ e⟩

section

variable {N N' : Type*} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
  (f : N →ₗ[R] N')

@[simp]
/-
**Module.FaithfullyFlat.lTensor_injective_iff_injective** 是 Mathlib 中的一个引理，位于命名空
间 `Module.FaithfullyFlat`。
形式化陈述：lTensor_injective_iff_injective [Module.FaithfullyFlat R M] : Function.Inj
ective (f.lTensor M) ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.exact_zero_iff_injective`：exact_zero_iff_injective {M N : Type
*} (P : Type*) [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N] 
[Module R M] [Module R P…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Module.FaithfullyFlat.lTensor_exact_iff_exact`：lTensor_exact_iff_exact [
FaithfullyFlat R M] : Function.Exact (l12.lTensor M) (l23.lTensor M) ↔ Function.
Exact l12 l23
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.lTensor_zero`：lTensor_zero : lTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lTensor_injective_iff_injective [Module.FaithfullyFlat R M] :
    Function.Injective (f.lTensor M) ↔ Function.Injective f := by
  rw [← LinearMap.exact_zero_iff_injective (M ⊗[R] Unit), ← LinearMap.exact_zero_iff_injective Unit]
  conv_rhs => rw [← lTensor_exact_iff_exact R M]
  simp

@[simp]
/-
**Module.FaithfullyFlat.lTensor_surjective_iff_surjective** 是 Mathlib 中的一个引理，位于命
名空间 `Module.FaithfullyFlat`。
形式化陈述：lTensor_surjective_iff_surjective [Module.FaithfullyFlat R M] : Function.S
urjective (f.lTensor M) ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.exact_zero_iff_surjective`：exact_zero_iff_surjective {M N : Ty
pe*} (P : Type*) [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N
] [Module R M] [Module R …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Module.FaithfullyFlat.lTensor_exact_iff_exact`：lTensor_exact_iff_exact [
FaithfullyFlat R M] : Function.Exact (l12.lTensor M) (l23.lTensor M) ↔ Function.
Exact l12 l23
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.lTensor_zero`：lTensor_zero : lTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lTensor_surjective_iff_surjective [Module.FaithfullyFlat R M] :
    Function.Surjective (f.lTensor M) ↔ Function.Surjective f := by
  rw [← LinearMap.exact_zero_iff_surjective (M ⊗[R] Unit),
    ← LinearMap.exact_zero_iff_surjective Unit]
  conv_rhs => rw [← lTensor_exact_iff_exact R M]
  simp

@[simp]
/-
**Module.FaithfullyFlat.lTensor_bijective_iff_bijective** 是 Mathlib 中的一个引理，位于命名空
间 `Module.FaithfullyFlat`。
形式化陈述：lTensor_bijective_iff_bijective [Module.FaithfullyFlat R M] : Function.Bij
ective (f.lTensor M) ↔ Function.Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lTensor_bijective_iff_bijective [Module.FaithfullyFlat R M] :
    Function.Bijective (f.lTensor M) ↔ Function.Bijective f := by
  simp [Function.Bijective]

end

end arbitrary_universe

section fixed_universe

/-
**Module.FaithfullyFlat.iff_exact_iff_rTensor_exact** 是 Mathlib 中的一个引理，位于命名空间 `M
odule.FaithfullyFlat`。
形式化陈述：iff_exact_iff_rTensor_exact : FaithfullyFlat R M ↔ (forall {N1 : Type max 
u v} [AddCommGroup N1] [Module R N1] {N2 : Type max u v} [AddCommGroup N2] [Modu
le R N2] {N3 : Type max u v} [AddCommGroup N3] [Module R N3] (l12 : N1 ->ₗ[R] N2
) (l23 : N2 ->ₗ[R] N3), Function.Exact l12 l23 ↔ Function.Exact (l12.rTensor M) 
(l23.rTensor M))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Module.FaithfullyFlat.rTensor_exact_iff_exact`：rTensor_exact_iff_exact [
FaithfullyFlat R M] : Function.Exact (l12.rTensor M) (l23.rTensor M) ↔ Function.
Exact l12 l23
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality`：iff_flat
_and_rTensor_reflects_triviality : FaithfullyFlat R M ↔ (Flat R M ∧ forall (N : 
Type max u v) [AddCommGroup N] [Module R N], Subsing…
· 使用定理 `Module.Flat.iff_rTensor_exact`：iff_rTensor_exact : Flat R M ↔ forall ⦃N 
N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [
Module R N] [Module…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.rTensor_zero`：rTensor_zero : rTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma iff_exact_iff_rTensor_exact :
    FaithfullyFlat R M ↔
    (∀ {N1 : Type max u v} [AddCommGroup N1] [Module R N1]
      {N2 : Type max u v} [AddCommGroup N2] [Module R N2]
      {N3 : Type max u v} [AddCommGroup N3] [Module R N3]
      (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.rTensor M) (l23.rTensor M)) :=
  ⟨fun fl _ _ _ _ _ _ _ _ _ l12 l23 => (rTensor_exact_iff_exact R M l12 l23).symm, fun iff_exact =>
    iff_flat_and_rTensor_reflects_triviality _ _ |>.2
      ⟨Flat.iff_rTensor_exact.2 <| fun _ _ _ => iff_exact .. |>.1,
    fun N _ _ h => subsingleton_iff_forall_eq 0 |>.2 <| fun y => by
      simpa [eq_comm] using (iff_exact (0 : PUnit →ₗ[R] N) (0 : N →ₗ[R] PUnit) |>.2 fun x => by
        simpa using Subsingleton.elim _ _) y⟩⟩
/-
**Module.FaithfullyFlat.iff_exact_iff_lTensor_exact** 是 Mathlib 中的一个引理，位于命名空间 `M
odule.FaithfullyFlat`。
形式化陈述：iff_exact_iff_lTensor_exact : FaithfullyFlat R M ↔ (forall {N1 : Type max 
u v} [AddCommGroup N1] [Module R N1] {N2 : Type max u v} [AddCommGroup N2] [Modu
le R N2] {N3 : Type max u v} [AddCommGroup N3] [Module R N3] (l12 : N1 ->ₗ[R] N2
) (l23 : N2 ->ₗ[R] N3), Function.Exact l12 l23 ↔ Function.Exact (l12.lTensor M) 
(l23.lTensor M))
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iff_exact_iff_lTensor_exact :
    FaithfullyFlat R M ↔
    (∀ {N1 : Type max u v} [AddCommGroup N1] [Module R N1]
      {N2 : Type max u v} [AddCommGroup N2] [Module R N2]
      {N3 : Type max u v} [AddCommGroup N3] [Module R N3]
      (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.lTensor M) (l23.lTensor M)) := by
  simp only [iff_exact_iff_rTensor_exact, LinearMap.rTensor_exact_iff_lTensor_exact]

end fixed_universe

end exact

section linearMap

/-!
### Faithfully flat modules and linear maps

In this section we prove that an `R`-module `M` is faithfully flat iff the following holds:

- `M` is flat
- for any `R`-linear map `f : N → N'`, `f` = 0 iff `f ⊗ 𝟙M = 0` iff `𝟙M ⊗ f = 0`

-/

section arbitrary_universe

/--
If `M` is a faithfully flat module, then for all linear maps `f`, the map `id ⊗ f = 0`, if and only
if `f = 0`. -/
/-
**Module.FaithfullyFlat.zero_iff_lTensor_zero** 是 Mathlib 中的一个引理，位于命名空间 `Module.
FaithfullyFlat`。
形式化陈述：zero_iff_lTensor_zero [h : FaithfullyFlat R M] {N : Type*} [AddCommGroup N
] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N ->ₗ[R] N') : 
f = 0 ↔ LinearMap.lTensor M f = 0
参数：f : N ->ₗ[R] N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.lTensor_zero`：lTensor_zero : lTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.FaithfullyFlat.lTensor_reflects_exact`：lTensor_reflects_exact [fl
 : FaithfullyFlat R M] (ex : Function.Exact (l12.lTensor M) (l23.lTensor M)) : F
unction.Exact l12 l23
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `LinearMap.range_zero`：range_zero [RingHomSurjective τ₁₂] : range (0 : M 
->ₛₗ[τ₁₂] M₂) = ⊥
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p

--- 原说明 ---
If `M` is a faithfully flat module, then for all linear maps `f`, the map `id ⊗ 
f = 0`, if and only
if `f = 0`.
-/
lemma zero_iff_lTensor_zero [h : FaithfullyFlat R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') :
    f = 0 ↔ LinearMap.lTensor M f = 0 :=
  ⟨fun hf => hf.symm ▸ LinearMap.lTensor_zero M, fun hf => by
    have := lTensor_reflects_exact R M f LinearMap.id (by
      rw [LinearMap.exact_iff, hf, LinearMap.range_zero, LinearMap.ker_eq_bot]
      apply Module.Flat.lTensor_preserves_injective_linearMap
      exact fun _ _ h => h)
    ext x; simpa using this (f x)⟩


/--
If `M` is a faithfully flat module, then for all linear maps `f`, the map `f ⊗ id = 0`, if and only
if `f = 0`. -/
/-
**Module.FaithfullyFlat.zero_iff_rTensor_zero** 是 Mathlib 中的一个引理，位于命名空间 `Module.
FaithfullyFlat`。
形式化陈述：zero_iff_rTensor_zero [h: FaithfullyFlat R M] {N : Type*} [AddCommGroup N]
 [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N ->ₗ[R] N') : f
 = 0 ↔ LinearMap.rTensor M f = 0
参数：f : N ->ₗ[R] N'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Module.FaithfullyFlat.zero_iff_lTensor_zero`：zero_iff_lTensor_zero [h : 
FaithfullyFlat R M] {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddC
ommGroup N'] [Module R N'] (f : N…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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

--- 原说明 ---
If `M` is a faithfully flat module, then for all linear maps `f`, the map `f ⊗ i
d = 0`, if and only
if `f = 0`.
-/
lemma zero_iff_rTensor_zero [h: FaithfullyFlat R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {N' : Type*} [AddCommGroup N'] [Module R N']
    (f : N →ₗ[R] N') :
    f = 0 ↔ LinearMap.rTensor M f = 0 :=
  zero_iff_lTensor_zero R M f |>.trans
  ⟨fun h => by ext n m; exact (TensorProduct.comm R N' M).injective <|
    (by simpa using congr($h (m ⊗ₜ n))), fun h => by
    ext m n; exact (TensorProduct.comm R M N').injective <| (by simpa using congr($h (n ⊗ₜ m)))⟩

/-- If `A` is a faithfully flat `R`-algebra, and `m` is a term of an `R`-module `M`,
then `1 ⊗ₜ[R] m = 0` if and only if `m = 0`. -/
@[simp]
/-
**Module.FaithfullyFlat.one_tmul_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.F
aithfullyFlat`。
形式化陈述：one_tmul_eq_zero_iff {A : Type*} [Ring A] [Algebra R A] [FaithfullyFlat R 
A] (m : M) : (1 : A) otimesₜ[R] m = 0 ↔ m = 0
参数：m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.FaithfullyFlat.zero_iff_lTensor_zero`：zero_iff_lTensor_zero [h : 
FaithfullyFlat R M] {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddC
ommGroup N'] [Module R N'] (f : N…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0

--- 原说明 ---
If `A` is a faithfully flat `R`-algebra, and `m` is a term of an `R`-module `M`,
then `1 ⊗ₜ[R] m = 0` if and only if `m = 0`.
-/
theorem one_tmul_eq_zero_iff {A : Type*} [Ring A] [Algebra R A] [FaithfullyFlat R A] (m : M) :
    (1 : A) ⊗ₜ[R] m = 0 ↔ m = 0 := by
  constructor; swap
  · rintro rfl; rw [tmul_zero]
  intro h
  let f : R →ₗ[R] M := (LinearMap.lsmul R M).flip m
  suffices f = 0 by simpa [f] using DFunLike.congr_fun this 1
  rw [Module.FaithfullyFlat.zero_iff_lTensor_zero R A]
  ext a
  apply_fun (a • ·) at h
  rw [smul_zero, smul_tmul', smul_eq_mul, mul_one] at h
  simpa [f]

end arbitrary_universe

section fixed_universe

/--
An `R`-module `M` is faithfully flat iff it is flat and for all linear maps `f`, the map
`id ⊗ f = 0`, if and only if `f = 0`. -/
/-
**Module.FaithfullyFlat.iff_zero_iff_lTensor_zero** 是 Mathlib 中的一个引理，位于命名空间 `Mod
ule.FaithfullyFlat`。
形式化陈述：iff_zero_iff_lTensor_zero : FaithfullyFlat R M ↔ (Module.Flat R M ∧ (foral
l {N : Type max u v} [AddCommGroup N] [Module R N] {N' : Type max u v} [AddCommG
roup N'] [Module R N'] (f : N ->ₗ[R] N'), f.lTensor M = 0 ↔ f = 0))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Module.FaithfullyFlat.zero_iff_lTensor_zero`：zero_iff_lTensor_zero [h : 
FaithfullyFlat R M] {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddC
ommGroup N'] [Module R N'] (f : N…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality`：iff_flat
_and_lTensor_reflects_triviality : FaithfullyFlat R M ↔ (Flat R M ∧ forall (N : 
Type max u v) [AddCommGroup N] [Module R N], Subsing…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x

--- 原说明 ---
An `R`-module `M` is faithfully flat iff it is flat and for all linear maps `f`,
 the map
`id ⊗ f = 0`, if and only if `f = 0`.
-/
lemma iff_zero_iff_lTensor_zero :
    FaithfullyFlat R M ↔
    (Module.Flat R M ∧
      (∀ {N : Type max u v} [AddCommGroup N] [Module R N]
        {N' : Type max u v} [AddCommGroup N'] [Module R N']
        (f : N →ₗ[R] N'), f.lTensor M = 0 ↔ f = 0)) :=
  ⟨fun fl => ⟨inferInstance, fun f => zero_iff_lTensor_zero R M f |>.symm⟩,
    fun ⟨flat, Z⟩ => iff_flat_and_lTensor_reflects_triviality R M |>.2 ⟨flat, fun N _ _ _ => by
      have := Z (LinearMap.id : N →ₗ[R] N) |>.1 (by ext; exact Subsingleton.elim _ _)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y => congr($this y)⟩⟩

/--
An `R`-module `M` is faithfully flat iff it is flat and for all linear maps `f`, the map
`id ⊗ f = 0`, if and only if `f = 0`. -/
/-
**Module.FaithfullyFlat.iff_zero_iff_rTensor_zero** 是 Mathlib 中的一个引理，位于命名空间 `Mod
ule.FaithfullyFlat`。
形式化陈述：iff_zero_iff_rTensor_zero : FaithfullyFlat R M ↔ (Module.Flat R M ∧ (foral
l {N : Type max u v} [AddCommGroup N] [Module R N] {N' : Type max u v} [AddCommG
roup N'] [Module R N'] (f : N ->ₗ[R] N'), f.rTensor M = 0 ↔ (f = 0)))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Module.FaithfullyFlat.zero_iff_rTensor_zero`：zero_iff_rTensor_zero [h: F
aithfullyFlat R M] {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCo
mmGroup N'] [Module R N'] (f : N …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality`：iff_flat
_and_rTensor_reflects_triviality : FaithfullyFlat R M ↔ (Flat R M ∧ forall (N : 
Type max u v) [AddCommGroup N] [Module R N], Subsing…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x

--- 原说明 ---
An `R`-module `M` is faithfully flat iff it is flat and for all linear maps `f`,
 the map
`id ⊗ f = 0`, if and only if `f = 0`.
-/
lemma iff_zero_iff_rTensor_zero :
    FaithfullyFlat R M ↔
    (Module.Flat R M ∧
      (∀ {N : Type max u v} [AddCommGroup N] [Module R N]
        {N' : Type max u v} [AddCommGroup N'] [Module R N']
        (f : N →ₗ[R] N'), f.rTensor M = 0 ↔ (f = 0))) :=
  ⟨fun fl => ⟨inferInstance, fun f => zero_iff_rTensor_zero R M f |>.symm⟩,
    fun ⟨flat, Z⟩ => iff_flat_and_rTensor_reflects_triviality R M |>.2 ⟨flat, fun N _ _ _ => by
      have := Z (LinearMap.id : N →ₗ[R] N) |>.1 (by ext; exact Subsingleton.elim _ _)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y => congr($this y)⟩⟩

end fixed_universe

end linearMap

section trans

open TensorProduct LinearMap

variable (R : Type*) [CommRing R]
variable (S : Type*) [CommRing S] [Algebra R S]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [FaithfullyFlat R S] [FaithfullyFlat S M]

include S in
/-- If `S` is a faithfully flat `R`-algebra, then any faithfully flat `S`-Module is faithfully flat
as an `R`-module. -/
/-
**Module.FaithfullyFlat.trans** 是 Mathlib 中的一个定理，位于命名空间 `Module.FaithfullyFlat`。
形式化陈述：trans : FaithfullyFlat R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.FaithfullyFlat.iff_zero_iff_lTensor_zero`：iff_zero_iff_lTensor_ze
ro : FaithfullyFlat R M ↔ (Module.Flat R M ∧ (forall {N : Type max u v} [AddComm
Group N] [Module R N] {N' : Type max …
· 使用定理 `Module.Flat.trans`：trans [Flat R S] [Flat S M] : Flat R M
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用引理 `Module.FaithfullyFlat.zero_iff_lTensor_zero`：zero_iff_lTensor_zero [h : 
FaithfullyFlat R M] {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddC
ommGroup N'] [Module R N'] (f : N…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.restrictScalars_inj`：restrictScalars_inj (fₗ gₗ : M ->ₗ[S] M₂)
 : fₗ.restrictScalars R = gₗ.restrictScalars R ↔ fₗ = gₗ
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearMap.lTensor_zero`：lTensor_zero : lTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `S` is a faithfully flat `R`-algebra, then any faithfully flat `S`-Module is 
faithfully flat
as an `R`-module.
-/
theorem trans : FaithfullyFlat R M := by
  rw [iff_zero_iff_lTensor_zero]
  refine ⟨Module.Flat.trans R S M, @fun N _ _ N' _ _ f => ⟨fun aux => ?_, fun eq => eq ▸ by simp⟩⟩
  rw [zero_iff_lTensor_zero (R := R) (M := S) f,
    show f.lTensor S = (AlgebraTensorModule.map (A := S) LinearMap.id f).restrictScalars R by aesop,
    show (0 :  S ⊗[R] N →ₗ[R] S ⊗[R] N') = (0 : S ⊗[R] N →ₗ[S] S ⊗[R] N').restrictScalars R by rfl,
    restrictScalars_inj, zero_iff_lTensor_zero (R := S) (M := M)]
  ext m n
  apply_fun AlgebraTensorModule.cancelBaseChange R S S M N' using LinearEquiv.injective _
  simpa using congr($aux (m ⊗ₜ[R] n))

end trans

/-- Faithful flatness is preserved by arbitrary base change. -/
/-
**Module.FaithfullyFlat.** 是 Mathlib 中的一个实例，位于命名空间 `Module.FaithfullyFlat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Faithful flatness is preserved by arbitrary base change.
-/
instance (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R M] :
    Module.FaithfullyFlat S (S ⊗[R] M) := by
  rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
  refine ⟨inferInstance, fun N _ _ hN ↦ ?_⟩
  let _ : Module R N := Module.compHom N (algebraMap R S)
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r ↦ congrFun rfl
  have := (AlgebraTensorModule.cancelBaseChange R S S N M).symm.subsingleton
  exact FaithfullyFlat.rTensor_reflects_triviality R M N

section IsBaseChange

variable {S N : Type*} [CommRing S] [Algebra R S] [FaithfullyFlat R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] {f : M →ₗ[R] N}

/-
**Module.FaithfullyFlat._root_.IsBaseChange.map_smul_top_ne_top_iff_of_faithfull
yFlat** 是 Mathlib 中的一个定理，位于命名空间 `Module.FaithfullyFlat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsBaseChange.map_smul_top_ne_top_iff_of_faithfullyFlat (hf : IsBaseChange S f)
    (I : Ideal R) :
    I.map (algebraMap R S) • (⊤ : Submodule S N) ≠ ⊤ ↔ I • (⊤ : Submodule R M) ≠ ⊤ := by
  simpa only [← Submodule.Quotient.subsingleton_iff.not] using not_congr <|
    (tensorQuotEquivQuotSMul N (I.map (algebraMap R S))).symm ≪≫ₗ TensorProduct.comm S N _ ≪≫ₗ
      hf.tensorEquiv _ ≪≫ₗ AlgebraTensorModule.congr (I.qoutMapEquivTensorQout S) (.refl R M) ≪≫ₗ
        AlgebraTensorModule.assoc R R S S _ M ≪≫ₗ (TensorProduct.comm R _ M).baseChange R S _ _ ≪≫ₗ
          (tensorQuotEquivQuotSMul M I).baseChange R S _ _ |>.subsingleton_congr.trans <|
            subsingleton_tensorProduct_iff_right R S

end IsBaseChange

end FaithfullyFlat

/-- Flat descends along faithfully flat ring maps. -/
/-
**Module.Flat.of_flat_tensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：∀ (R : Type u) (M : Type v) [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] (S : Type u_1)   [inst_3 : CommRing S] [inst_4 : Al
gebra R S] [Module.FaithfullyFlat R S] [Module.Flat S (TensorProduct R S M)],   
Module.Flat R M
参数：R : Type u；M : Type v；S : Type u_1；TensorProduct R S M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Flat.iff_lTensor_preserves_injective_linearMap`：iff_lTensor_prese
rves_injective_linearMap : Flat R M ↔ forall ⦃N N' : Type (max u v)⦄ [AddCommGro
up N] [AddCommGroup N'] [Module R N] [Modul…
· 使用定理 `Module.Flat.trans`：trans [Flat R S] [Flat S M] : Flat R M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.FaithfullyFlat.lTensor_injective_iff_injective`：lTensor_injective
_iff_injective [Module.FaithfullyFlat R M] : Function.Injective (f.lTensor M) ↔ 
Function.Injective f
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)

--- 原说明 ---
Flat descends along faithfully flat ring maps.
-/
lemma Flat.of_flat_tensorProduct (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [Module.Flat S (S ⊗[R] M)] : Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  have : Flat R (S ⊗[R] M) := Flat.trans _ S _
  rw [← FaithfullyFlat.lTensor_injective_iff_injective R S]
  have : LinearMap.lTensor S (LinearMap.lTensor M f) =
      (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ LinearMap.lTensor (S ⊗[R] M) f ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap := by
    ext
    simp
  simpa [this] using Flat.lTensor_preserves_injective_linearMap f hf
/-
**Module.Flat.iff_flat_tensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：∀ (R : Type u) (M : Type v) [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] (S : Type u_1)   [inst_3 : CommRing S] [inst_4 : Al
gebra R S] [Module.FaithfullyFlat R S],   Module.Flat S (TensorProduct R S M) ↔ 
Module.Flat R M
参数：R : Type u；M : Type v；S : Type u_1；TensorProduct R S M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Flat.of_flat_tensorProduct`：∀ (R : Type u) (M : Type v) [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (S : Type u_1)
   [inst_3 : CommRing S…
-/
lemma Flat.iff_flat_tensorProduct (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] : Module.Flat S (S ⊗[R] M) ↔ Module.Flat R M :=
  ⟨fun _ ↦ .of_flat_tensorProduct R M S, fun _ ↦ inferInstance⟩

end Module

namespace Submodule

open LinearMap Module

variable {R M A : Type*} [CommRing R] [Ring A] [Algebra R A] [FaithfullyFlat R A]
  [AddCommGroup M] [Module R M] {p q : Submodule R M}

@[simp]
/-
**Submodule.baseChange_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：baseChange_le_iff : p.baseChange A <= q.baseChange A ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `LinearMap.le_ker_iff_comp_subtype_eq_zero`：le_ker_iff_comp_subtype_eq_ze
ro {N : Submodule R M} {f : M ->ₛₗ[τ₁₂] M₂} : N <= ker f ↔ f ∘ₛₗ N.subtype = 0
· 使用引理 `Module.FaithfullyFlat.zero_iff_lTensor_zero`：zero_iff_lTensor_zero [h : 
FaithfullyFlat R M] {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddC
ommGroup N'] [Module R N'] (f : N…
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
· 使用定理 `LinearMap.range_le_ker_iff`：range_le_ker_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M
₂ ->ₛₗ[τ₂₃] M₃} : range f <= ker g ↔ (g.comp f : M ->ₛₗ[τ₁₃] M₃) = 0
· 使用引理 `lTensor_mkQ`：lTensor_mkQ (N : Submodule R M) : ker (lTensor Q N.mkQ) = r
ange (lTensor Q N.subtype)
· 使用定理 `Submodule.restrictScalars_le`：∀ (S : Type u_1) {R : Type u_2} {M : Type 
u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S]   [ins
t_3 : _root_.Modul…
· 使用定理 `Submodule.baseChange_mono`：baseChange_mono (h : p <= q) : p.baseChange A
 <= q.baseChange A
-/
theorem baseChange_le_iff : p.baseChange A ≤ q.baseChange A ↔ p ≤ q := by
  refine ⟨fun h ↦ ?_, baseChange_mono A⟩
  rwa [← q.ker_mkQ, le_ker_iff_comp_subtype_eq_zero, FaithfullyFlat.zero_iff_lTensor_zero R A,
    lTensor_comp, ← range_le_ker_iff, lTensor_mkQ, ← restrictScalars_le R]
/-
**Submodule.baseChange_inj** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：baseChange_inj : p.baseChange A = q.baseChange A ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem baseChange_inj : p.baseChange A = q.baseChange A ↔ p = q := by
  simp [le_antisymm_iff]
/-
**Submodule.baseChange_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：baseChange_injective (h : p.baseChange A = q.baseChange A) : p = q
参数：h : p.baseChange A = q.baseChange A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.baseChange_inj`：baseChange_inj : p.baseChange A = q.baseChange
 A ↔ p = q
-/
theorem baseChange_injective (h : p.baseChange A = q.baseChange A) : p = q :=
  baseChange_inj.mp h

variable (R M A) in
/-- `Submodule.baseChange` as an order embedding. -/
@[simps]
/-
**Submodule.baseChangeOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：baseChangeOrderEmbedding : Submodule R M ↪o Submodule A (A otimes[R] M) wh
ere toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.baseChange_injective`：baseChange_injective (h : p.baseChange A
 = q.baseChange A) : p = q
· 使用定理 `Submodule.baseChange_le_iff`：baseChange_le_iff : p.baseChange A <= q.bas
eChange A ↔ p <= q

--- 原说明 ---
`Submodule.baseChange` as an order embedding.
-/
def baseChangeOrderEmbedding : Submodule R M ↪o Submodule A (A ⊗[R] M) where
  toFun := baseChange A
  inj' _ _ := baseChange_injective
  map_rel_iff' := baseChange_le_iff
/-
**Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat** 是 Mat
hlib 中的一个定理，位于命名空间 `Submodule.IsNoetherian`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {A : Type u_3} [inst : CommRing R] [inst_1
 : Ring A] [inst_2 : Algebra R A]   [Module.FaithfullyFlat R A] [inst_4 : AddCom
mGroup M] [inst_5 : _root_.Module R M],   IsNoetherian A (TensorProduct R A M) →
 IsNoetherian R M
参数：TensorProduct R A M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isNoetherian_iff'`：isNoetherian_iff' : IsNoetherian R M ↔ WellFoundedGT 
(Submodule R M)
· 使用定理 `OrderEmbedding.wellFoundedGT`：∀ {α : Type u_2} {β : Type u_3} [inst : Pr
eorder α] [inst_1 : Preorder β] [WellFoundedGT β] (f : α ↪o β),   WellFoundedGT 
α
-/
theorem IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (h : IsNoetherian A (A ⊗[R] M)) : IsNoetherian R M := by
  rw [isNoetherian_iff'] at h ⊢
  exact (baseChangeOrderEmbedding R M A).wellFoundedGT
/-
**Submodule.IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat** 是 Mathlib
 中的一个定理，位于命名空间 `Submodule.IsArtinian`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {A : Type u_3} [inst : CommRing R] [inst_1
 : Ring A] [inst_2 : Algebra R A]   [Module.FaithfullyFlat R A] [inst_4 : AddCom
mGroup M] [inst_5 : _root_.Module R M],   IsArtinian A (TensorProduct R A M) → I
sArtinian R M
参数：TensorProduct R A M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `OrderEmbedding.wellFoundedLT`：∀ {α : Type u_2} {β : Type u_3} [inst : Pr
eorder α] [inst_1 : Preorder β] [WellFoundedLT β] (f : α ↪o β),   WellFoundedLT 
α
-/
theorem IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat
    (h : IsArtinian A (A ⊗[R] M)) : IsArtinian R M :=
  (baseChangeOrderEmbedding R M A).wellFoundedLT

end Submodule

