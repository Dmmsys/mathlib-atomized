/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
module

public import Mathlib.Algebra.Module.Submodule.IterateMapComap
public import Mathlib.Order.PartialSups
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.OrzechProperty

/-!
# Noetherian rings have the Orzech property

## Main results

* `IsNoetherian.injective_of_surjective_of_injective`: if `M` and `N` are `R`-modules for a ring `R`
  (not necessarily commutative), `M` is Noetherian, `i : N →ₗ[R] M` is injective,
  `f : N →ₗ[R] M` is surjective, then `f` is also injective.
* `IsNoetherianRing.orzechProperty`: Any Noetherian ring satisfies the Orzech property.
-/

@[expose] public section


open Set Filter Pointwise

open IsNoetherian Submodule Function

section

universe w

variable {R M P : Type*} {N : Type w} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P] [IsNoetherian R M]

/-- **Orzech's theorem** for Noetherian modules: if `R` is a ring (not necessarily commutative),
`M` and `N` are `R`-modules, `M` is Noetherian, `i : N →ₗ[R] M` is injective,
`f : N →ₗ[R] M` is surjective, then `f` is also injective. The proof here is adapted from
Djoković's paper *Epimorphisms of modules which must be isomorphisms* [djokovic1973],
utilizing `LinearMap.iterateMapComap`.
See also Orzech's original paper: *Onto endomorphisms are isomorphisms* [orzech1971]. -/
/-
**IsNoetherian.injective_of_surjective_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsNoetherian.injective_of_surjective_of_injective (i f : N ->ₗ[R] M) (hi :
 Injective i) (hf : Surjective f) : Injective f
参数：i f : N ->ₗ[R] M；hi : Injective i；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_injective`：isNoetherian_of_injective [IsNoetherian S P] 
{σ : R ->+* S} {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : 
M ->ₛₗ[σ] P) (h…
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `LinearMap.iterateMapComap_le_succ`：iterateMapComap_le_succ (K : Submodul
e R N) (h : K.map f <= K.map i) (n : Nat) : f.iterateMapComap i n K <= f.iterate
MapComap i (n + 1) K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_stabilizes_iff_noetherian`：monotone_stabilizes_iff_noetherian :
 (forall f : Nat ->o Submodule R M, exists n, forall m, n <= m -> f n = f m) ↔ I
sNoetherian R M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `LinearMap.ker_le_of_iterateMapComap_eq_succ`：ker_le_of_iterateMapComap_e
q_succ (K : Submodule R N) (m : Nat) (heq : f.iterateMapComap i m K = f.iterateM
apComap i (m + 1) K) (hf : Surjec…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
**Orzech's theorem** for Noetherian modules: if `R` is a ring (not necessarily c
ommutative),
`M` and `N` are `R`-modules, `M` is Noetherian, `i : N →ₗ[R] M` is injective,
`f : N →ₗ[R] M` is surjective, then `f` is also injective. The proof here is ada
pted from
Djoković's paper *Epimorphisms of modules which must be isomorphisms* [djokovic1
973],
utilizing `LinearMap.iterateMapComap`.
See also Orzech's original paper: *Onto endomorphisms are isomorphisms* [orzech1
971].
-/
theorem IsNoetherian.injective_of_surjective_of_injective (i f : N →ₗ[R] M)
    (hi : Injective i) (hf : Surjective f) : Injective f := by
  have := isNoetherian_of_injective i hi
  obtain ⟨n, H⟩ := monotone_stabilizes_iff_noetherian.2 ‹_›
    ⟨_, monotone_nat_of_le_succ <| f.iterateMapComap_le_succ i ⊥ (by simp)⟩
  exact LinearMap.ker_eq_bot.1 <| bot_unique <|
    f.ker_le_of_iterateMapComap_eq_succ i ⊥ n (H _ (Nat.le_succ _)) hf hi

/-- **Orzech's theorem** for Noetherian modules: if `R` is a ring (not necessarily commutative),
`M` is a Noetherian `R`-module, `N` is a submodule, `f : N →ₗ[R] M` is surjective, then `f` is also
injective. -/
/-
**IsNoetherian.injective_of_surjective_of_submodule** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsNoetherian.injective_of_surjective_of_submodule {N : Submodule R M} (f :
 N ->ₗ[R] M) (hf : Surjective f) : Injective f
参数：f : N ->ₗ[R] M；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.injective_of_surjective_of_injective`：IsNoetherian.injectiv
e_of_surjective_of_injective (i f : N ->ₗ[R] M) (hi : Injective i) (hf : Surject
ive f) : Injective f
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype

--- 原说明 ---
**Orzech's theorem** for Noetherian modules: if `R` is a ring (not necessarily c
ommutative),
`M` is a Noetherian `R`-module, `N` is a submodule, `f : N →ₗ[R] M` is surjectiv
e, then `f` is also
injective.
-/
theorem IsNoetherian.injective_of_surjective_of_submodule
    {N : Submodule R M} (f : N →ₗ[R] M) (hf : Surjective f) : Injective f :=
  IsNoetherian.injective_of_surjective_of_injective N.subtype f N.injective_subtype hf

/-- Any surjective endomorphism of a Noetherian module is injective. -/
/-
**IsNoetherian.injective_of_surjective_endomorphism** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsNoetherian.injective_of_surjective_endomorphism (f : M ->ₗ[R] M) (s : Su
rjective f) : Injective f
参数：f : M ->ₗ[R] M；s : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.injective_of_surjective_of_injective`：IsNoetherian.injectiv
e_of_surjective_of_injective (i f : N ->ₗ[R] M) (hi : Injective i) (hf : Surject
ive f) : Injective f
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
Any surjective endomorphism of a Noetherian module is injective.
-/
theorem IsNoetherian.injective_of_surjective_endomorphism (f : M →ₗ[R] M)
    (s : Surjective f) : Injective f :=
  IsNoetherian.injective_of_surjective_of_injective _ f (LinearEquiv.refl _ _).injective s

/-- Any surjective endomorphism of a Noetherian module is bijective. -/
/-
**IsNoetherian.bijective_of_surjective_endomorphism** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsNoetherian.bijective_of_surjective_endomorphism (f : M ->ₗ[R] M) (s : Su
rjective f) : Bijective f
参数：f : M ->ₗ[R] M；s : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.injective_of_surjective_endomorphism`：IsNoetherian.injectiv
e_of_surjective_endomorphism (f : M ->ₗ[R] M) (s : Surjective f) : Injective f

--- 原说明 ---
Any surjective endomorphism of a Noetherian module is bijective.
-/
theorem IsNoetherian.bijective_of_surjective_endomorphism (f : M →ₗ[R] M)
    (s : Surjective f) : Bijective f :=
  ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩

/-- If `M ⊕ N` embeds into `M`, for `M` Noetherian over `R`, then `N` is trivial. -/
/-
**IsNoetherian.subsingleton_of_prod_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNoetherian.subsingleton_of_prod_injective (f : M × N ->ₗ[R] M) (i : Inje
ctive f) : Subsingleton N
参数：f : M × N ->ₗ[R] M；i : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.injective_of_surjective_of_injective`：IsNoetherian.injectiv
e_of_surjective_of_injective (i f : N ->ₗ[R] M) (hi : Injective i) (hf : Surject
ive f) : Injective f
· 使用定理 `LinearMap.fst_surjective`：fst_surjective : Function.Surjective (fst R M 
M₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
If `M ⊕ N` embeds into `M`, for `M` Noetherian over `R`, then `N` is trivial.
-/
theorem IsNoetherian.subsingleton_of_prod_injective (f : M × N →ₗ[R] M)
    (i : Injective f) : Subsingleton N := .intro fun x y ↦ by
  have h := IsNoetherian.injective_of_surjective_of_injective f _ i LinearMap.fst_surjective
  simpa using h (show LinearMap.fst R M N (0, x) = LinearMap.fst R M N (0, y) from rfl)

/-- If `M ⊕ N` embeds into `M`, for `M` Noetherian over `R`, then `N` is trivial. -/
@[simps!]
/-
**IsNoetherian.equivPUnitOfProdInjective** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsNoetherian.equivPUnitOfProdInjective (f : M × N ->ₗ[R] M) (i : Injective
 f) : N ≃ₗ[R] PUnit.{w + 1}
参数：f : M × N ->ₗ[R] M；i : Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.subsingleton_of_prod_injective`：IsNoetherian.subsingleton_o
f_prod_injective (f : M × N ->ₗ[R] M) (i : Injective f) : Subsingleton N
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}

--- 原说明 ---
If `M ⊕ N` embeds into `M`, for `M` Noetherian over `R`, then `N` is trivial.
-/
def IsNoetherian.equivPUnitOfProdInjective (f : M × N →ₗ[R] M)
    (i : Injective f) : N ≃ₗ[R] PUnit.{w + 1} :=
  haveI := IsNoetherian.subsingleton_of_prod_injective f i
  .ofSubsingleton _ _

end

/-- Any Noetherian ring satisfies Orzech property.
See also `IsNoetherian.injective_of_surjective_of_submodule` and
`IsNoetherian.injective_of_surjective_of_injective`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any Noetherian ring satisfies Orzech property.
See also `IsNoetherian.injective_of_surjective_of_submodule` and
`IsNoetherian.injective_of_surjective_of_injective`.
-/
instance (priority := 100) IsNoetherianRing.orzechProperty
    (R) [Ring R] [IsNoetherianRing R] : OrzechProperty R where
  injective_of_surjective_of_submodule' {M} :=
    letI := Module.addCommMonoidToAddCommGroup R (M := M)
    IsNoetherian.injective_of_surjective_of_submodule
