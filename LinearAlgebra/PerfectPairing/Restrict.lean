/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.BaseChange

/-!
# Restriction to submodules and restriction of scalars for perfect pairings.

We provide API for restricting perfect pairings to submodules and for restricting their scalars.

## Main definitions
* `PerfectPairing.restrict`: restriction of a perfect pairing to submodules.
* `PerfectPairing.restrictScalars`: restriction of scalars for a perfect pairing taking values in a
  subring.
* `PerfectPairing.restrictScalarsField`: simultaneously restrict both the domains and scalars
  of a perfect pairing with coefficients in a field.

-/

public section

open Function Module Set
open Submodule (span subset_span)

noncomputable section

namespace LinearMap

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair]

section Restrict

variable {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  (i : M' →ₗ[R] M) (j : N' →ₗ[R] N) (hi : Injective i) (hj : Injective j)
  (hij : p.IsPerfectCompl (LinearMap.range i) (LinearMap.range j))

include hi hj hij

/-
**LinearMap.restrict_aux** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma restrict_aux : Bijective (p.compl₁₂ i j) := by
  refine ⟨LinearMap.ker_eq_bot.mp <| eq_bot_iff.mpr fun m hm ↦ ?_, fun f ↦ ?_⟩
  · replace hm : i m ∈ j.range.dualAnnihilator.map (p.toPerfPair.symm : Dual R N →ₗ[R] M) := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator]
      refine ⟨p.toPerfPair (i m), ?_, LinearEquiv.symm_apply_apply _ _⟩
      rintro - ⟨n, rfl⟩
      simpa using LinearMap.congr_fun hm n
    suffices i m ∈ (⊥ : Submodule R M) by simpa [hi] using this
    simpa only [← hij.isCompl_left.inf_eq_bot, Submodule.mem_inf]
      using ⟨LinearMap.mem_range_self i m, hm⟩
  · set F : Module.Dual R N := f ∘ₗ j.linearProjOfIsCompl _ hj hij.isCompl_right with hF
    have hF (n : N') : F (j n) = f n := by simp [hF]
    set m : M := p.toPerfPair.symm F with hm
    obtain ⟨-, y, ⟨m₀, rfl⟩, hy, hm'⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hij.isCompl_left.codisjoint m
    refine ⟨m₀, LinearMap.ext fun n ↦ ?_⟩
    replace hy : (p y) (j n) = 0 := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      simpa using hg _ (LinearMap.mem_range_self j n)
    rw [hm, ← LinearEquiv.symm_apply_eq, map_add, LinearEquiv.symm_symm] at hm'
    simpa [← hF, ← LinearMap.congr_fun hm' (j n)]

/-- The restriction of a perfect pairing to submodules is a perfect pairing. -/
/-
**LinearMap.IsPerfPair.restrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPerfPair`
。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup N] [ins
t_4 : _root_.Module R N] (p : M →ₗ[R] N →ₗ[R] R)   [inst_5 : p.IsPerfPair] {M' :
 Type u_4} {N' : Type u_5} [inst_6 : AddCommGroup M'] [inst_7 : _root_.Module R 
M']   [inst_8 : AddCommGroup N'] [inst_9 : _root_.Module R N'] (i : M' →ₗ[R] M) 
(j : N' →ₗ[R] N),   Function.Injective ⇑i → Function.Injective ⇑j → p.IsPerfectC
ompl i.range j.range → (p.compl₁₂ i j).IsPerfPair
参数：p : M →ₗ[R] N →ₗ[R] R；i : M' →ₗ[R] M；j : N' →ₗ[R] N；p.compl₁₂ i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `_private.Mathlib.LinearAlgebra.PerfectPairing.Restrict.0.LinearMap.restr
ict_aux`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [ins
t_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCom…
· 使用定理 `LinearMap.flip.instIsPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : Type
 u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   
[inst_3 : _root_.Mo…
· 使用定理 `LinearMap.IsPerfectCompl.flip`：∀ {R : Type u_1} {M : Type u_2} {N : Type
 u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R 
M] [inst_3 : AddCom…

--- 原说明 ---
The restriction of a perfect pairing to submodules is a perfect pairing.
-/
lemma IsPerfPair.restrict : (p.compl₁₂ i j).IsPerfPair where
  bijective_left := p.restrict_aux i j hi hj hij
  bijective_right := p.flip.restrict_aux j i hj hi hij.flip

end Restrict

section RestrictScalars

variable {S M' N' : Type*}
  [CommRing S] [IsDomain S] [Algebra S R] [Module S M] [Module S N] [IsScalarTower S R M]
  [IsScalarTower S R N] [IsTorsionFree S R] [Nontrivial R]
  [AddCommGroup M'] [Module S M'] [AddCommGroup N'] [Module S N']
  (i : M' →ₗ[S] M) (j : N' →ₗ[S] N)

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.restrictScalars_injective_aux** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma restrictScalars_injective_aux
    (hi : Injective i)
    (hN : span R (LinearMap.range j : Set N) = ⊤)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    Injective ((LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p hp)) := by
  let f := LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p hp
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun x (hx : f x = 0) ↦ ?_
  replace hx (n : N) : p (i x) n = 0 := by
    have hn : n ∈ span R (LinearMap.range j : Set N) := hN ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n', rfl⟩ := hz
      simpa [f] using LinearMap.congr_fun hx n'
    | zero => simp
    | add => rw [map_add]; aesop
    | smul => rw [map_smul]; aesop
  rw [← i.map_eq_zero_iff hi, ← p.map_eq_zero_iff p.toPerfPair.injective]
  ext n
  simpa using hx n

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.restrictScalars_surjective_aux** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma restrictScalars_surjective_aux
    (h : ∀ g : Module.Dual S N', ∃ m,
      (p.toPerfPair (i m)).restrictScalars S ∘ₗ j = Algebra.linearMap S R ∘ₗ g)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    Surjective ((LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p hp)) := by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_iff'.mpr fun g : Module.Dual S N' ↦ ?_
  obtain ⟨m, hm⟩ := h g
  refine ⟨m, ?_⟩
  ext n
  apply FaithfulSMul.algebraMap_injective S R
  change Algebra.linearMap S R _ = _
  simpa using LinearMap.congr_fun hm n

/-- Restricting a perfect pairing to a subring of the scalars results in a perfect pairing. -/
/-
**LinearMap.IsPerfPair.restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPe
rfPair`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup N] [ins
t_4 : _root_.Module R N] (p : M →ₗ[R] N →ₗ[R] R)   [inst_5 : p.IsPerfPair] {S : 
Type u_4} {M' : Type u_5} {N' : Type u_6} [inst_6 : CommRing S] [inst_7 : IsDoma
in S]   [inst_8 : Algebra S R] [inst_9 : _root_.Module S M] [inst_10 : _root_.Mo
dule S N] [inst_11 : IsScalarTower S R M]   [inst_12 : IsScalarTower S R N] [ins
t_13 : Module.IsTorsionFree S R] [inst_14 : Nontrivial R]   [inst_15 : AddCommGr
oup M'] [inst_16 : _root_.Module S M'] [inst_17 : AddCommGroup N'] [inst_18 : _r
oot_.Module S N']   (i : M' →ₗ[S] M) (j : N' →ₗ[S] N),   Function.Injective ⇑i →
     Function.Injective ⇑j →       Submodule.span R ↑i.range = ⊤ →         Submo
dule.span R ↑j.range = ⊤ →           (∀ (g : Module.Dual S N'), ∃ m, ↑S (p.toPer
fPair (i m)) ∘ₗ j = Algebra.linearMap S R ∘ₗ g) →             (∀ (g : Module.Dua
l S M'), ∃ n, ↑S (p.flip.toPerfPair (j n)) ∘ₗ i = Algebra.linearMap S R ∘ₗ g) → 
              ∀ (hp : ∀ (m : M') (n : N'), (p (i m)) (j n) ∈ (algebraMap S R).ra
nge),                 (i.restrictScalarsRange₂ j (Algebra.linearMap S R) ⋯ p hp)
.IsPerfPair
参数：p : M →ₗ[R] N →ₗ[R] R；i : M' →ₗ[S] M；j : N' →ₗ[S] N；∀ (g : Module.Dual S N'),
 ∃ m, ↑S (p.toPerfPair (i m)) ∘ₗ j = Algebra.linearMap S R ∘ₗ g；∀ (g : Module.Du
al S M'), ∃ n, ↑S (p.flip.toPerfPair (j n)) ∘ₗ i = Algebra.linearMap S R ∘ₗ g；hp
 : ∀ (m : M') (n : N'), (p (i m)) (j n) ∈ (algebraMap S R).range；i.restrictScala
rsRange₂ j (Algebra.linearMap S R) ⋯ p hp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.flip.instIsPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : Type
 u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   
[inst_3 : _root_.Mo…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `_private.Mathlib.LinearAlgebra.PerfectPairing.Restrict.0.LinearMap.restr
ictScalars_injective_aux`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst :
 CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : 
AddCom…
· 使用定理 `_private.Mathlib.LinearAlgebra.PerfectPairing.Restrict.0.LinearMap.restr
ictScalars_surjective_aux`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst 
: CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 :
 AddCom…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b

--- 原说明 ---
Restricting a perfect pairing to a subring of the scalars results in a perfect p
airing.
-/
lemma IsPerfPair.restrictScalars (hi : Injective i) (hj : Injective j)
    (hM : span R (LinearMap.range i : Set M) = ⊤) (hN : span R (LinearMap.range j : Set N) = ⊤)
    (h₁ : ∀ g : Module.Dual S N', ∃ m,
      (p.toPerfPair (i m)).restrictScalars S ∘ₗ j = Algebra.linearMap S R ∘ₗ g)
    (h₂ : ∀ g : Module.Dual S M', ∃ n,
      (p.flip.toPerfPair (j n)).restrictScalars S ∘ₗ i = Algebra.linearMap S R ∘ₗ g)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    (LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p hp).IsPerfPair where
  bijective_left := ⟨p.restrictScalars_injective_aux i j hi hN hp,
    p.restrictScalars_surjective_aux i j h₁ hp⟩
  bijective_right := ⟨p.flip.restrictScalars_injective_aux j i hj hM fun m n ↦ hp n m,
    p.flip.restrictScalars_surjective_aux j i h₂ fun m n ↦ hp n m⟩

end RestrictScalars

end CommRing

section Field

variable {K L M N : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  [Module K M] [Module K N] [IsScalarTower K L M]
  (p : M →ₗ[L] N →ₗ[L] L) [p.IsPerfPair]

set_option backward.isDefEq.respectTransparency false in
/-- If a perfect pairing over a field `L` takes values in a subfield `K` along two `K`-subspaces
whose `L` span is full, then these subspaces induce a `K`-structure in the sense of
[*Algebra I*, Bourbaki : Chapter II, §8.1 Definition 1][bourbaki1989]. -/
/-
**LinearMap.exists_basis_basis_of_span_eq_top_of_mem_algebraMap** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap`。
形式化陈述：exists_basis_basis_of_span_eq_top_of_mem_algebraMap (M' : Submodule K M) (
N' : Submodule K N) (hM : span L (M' : Set M) = ⊤) (hN : span L (N' : Set N) = ⊤
) (hp : forallᵉ (x in M') (y in N'), p x y in (algebraMap K L).range) : exists (
n : Nat) (b : Basis (Fin n) L M) (b' : Basis (Fin n) K M'), forall i, b i = b' i
参数：M' : Submodule K M；N' : Submodule K N；hM : span L (M' : Set M) = ⊤；hN : span 
L (N' : Set N) = ⊤；hp : forallᵉ (x in M') (y in N'), p x y in (algebraMap K L).r
ange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `LinearMap.flip.instIsPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : Type
 u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   
[inst_3 : _root_.Mo…
· 使用定理 `exists_linearIndependent`：exists_linearIndependent : exists b subseteq t
, span K b = span K t ∧ LinearIndependent K ((↑) : b -> V)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Module.Finite.finite_basis`：finite_basis [Nontrivial R] {ι} [Module.Fini
te R M] (b : Basis ι R M) : _root_.Finite ι
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Module.instFiniteDimensionalOfIsReflexive`：∀ (K : Type u_4) (V : Type u_
5) [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [Mo
dule.IsReflexive K V], FiniteDi…
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
· 使用定理 `LinearIndependent.restrict_scalars`：LinearIndependent.restrict_scalars [
Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] (hinj : Inject
ive fun r : R => r • (1 …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
If a perfect pairing over a field `L` takes values in a subfield `K` along two `
K`-subspaces
whose `L` span is full, then these subspaces induce a `K`-structure in the sense
 of
[*Algebra I*, Bourbaki : Chapter II, §8.1 Definition 1][bourbaki1989].
-/
lemma exists_basis_basis_of_span_eq_top_of_mem_algebraMap
    (M' : Submodule K M) (N' : Submodule K N)
    (hM : span L (M' : Set M) = ⊤)
    (hN : span L (N' : Set N) = ⊤)
    (hp : ∀ᵉ (x ∈ M') (y ∈ N'), p x y ∈ (algebraMap K L).range) :
    ∃ (n : ℕ) (b : Basis (Fin n) L M) (b' : Basis (Fin n) K M'), ∀ i, b i = b' i := by
  classical
  have : IsReflexive L M := .of_isPerfPair p
  have : IsReflexive L N := .of_isPerfPair p.flip
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := exists_linearIndependent L (M' : Set M)
  rw [hM] at hv₂
  let b : Basis _ L M := Basis.mk hv₃ <| by rw [← hv₂, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
  have : Fintype v := Set.Finite.fintype <| Module.Finite.finite_basis b
  set v' : v → M' := fun i ↦ ⟨i, hv₁ (Subtype.coe_prop i)⟩
  have hv' : LinearIndependent K v' := by
    replace hv₃ := hv₃.restrict_scalars (R := K) <| by
      simp_rw [← Algebra.algebraMap_eq_smul_one]
      exact FaithfulSMul.algebraMap_injective K L
    rw [show ((↑) : v → M) = M'.subtype ∘ v' by ext; simp [v']] at hv₃
    exact hv₃.of_comp
  suffices span K (Set.range v') = ⊤ by
    let e := (Module.Finite.finite_basis b).equivFin
    let b' : Basis _ K M' := Basis.mk hv' (by rw [this])
    exact ⟨_, b.reindex e, b'.reindex e, fun i ↦ by simp [b, b', v']⟩
  suffices span K v = M' by
    apply Submodule.map_injective_of_injective M'.injective_subtype
    rw [Submodule.map_span, ← Set.image_univ, Set.image_image]
    simpa [v']
  refine le_antisymm (Submodule.span_le.mpr hv₁) fun m hm ↦ ?_
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := exists_linearIndependent L (N' : Set N)
  rw [hN] at hw₂
  let bN : Basis _ L N := Basis.mk hw₃ <| by
    rw [← hw₂, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
  have : Fintype w := Set.Finite.fintype <| Module.Finite.finite_basis bN
  have e : v ≃ w := Fintype.equivOfCardEq <| by rw [← Module.finrank_eq_card_basis b,
    ← Module.finrank_eq_card_basis bN, Module.finrank_of_isPerfPair p]
  let bM := bN.dualBasis.map p.toPerfPair.symm
  have hbM (j : w) (x : M) (hx : x ∈ M') : bM.repr x j = p x (j : N) := by simp [bM, bN]
  have hj (j : w) : bM.repr m j ∈ (algebraMap K L).range := (hbM _ _ hm) ▸ hp m hm j (hw₁ j.2)
  replace hp (i : w) (j : v) :
      (bN.dualBasis.map p.toPerfPair.symm).toMatrix b i j ∈ (algebraMap K L).fieldRange := by
    simp only [Basis.toMatrix, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
      Basis.dualBasis_repr]
    exact hp (b j) (by simpa [b] using hv₁ j.2) (bN i) (by simpa [bN] using hw₁ i.2)
  have hA (i j) : b.toMatrix bM i j ∈ (algebraMap K L).range :=
    Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left e _ (by simp [bM]) hp i j
  have h_span : span K v = span K (Set.range b) := by simp [b]
  rw [h_span, Basis.mem_span_iff_repr_mem, ← Basis.toMatrix_mulVec_repr bM b m]
  exact fun i ↦ Subring.sum_mem _ fun j _ ↦ Subring.mul_mem _ (hA i j) (hj j)
/-
**LinearMap.finrank_eq_of_isPerfPair** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：finrank_eq_of_isPerfPair (M' : Submodule K M) (N' : Submodule K N) (hM : s
pan L (M' : Set M) = ⊤) (hN : span L (N' : Set N) = ⊤) (hp : forallᵉ (x in M') (
y in N'), p x y in (algebraMap K L).range) : finrank K M' = finrank L M
参数：M' : Submodule K M；N' : Submodule K N；hM : span L (M' : Set M) = ⊤；hN : span 
L (N' : Set N) = ⊤；hp : forallᵉ (x in M') (y in N'), p x y in (algebraMap K L).r
ange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LinearMap.exists_basis_basis_of_span_eq_top_of_mem_algebraMap`：exists_ba
sis_basis_of_span_eq_top_of_mem_algebraMap (M' : Submodule K M) (N' : Submodule 
K N) (hM : span L (M' : Set M) = ⊤) (hN : span L (N…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
lemma finrank_eq_of_isPerfPair
    (M' : Submodule K M) (N' : Submodule K N)
    (hM : span L (M' : Set M) = ⊤)
    (hN : span L (N' : Set N) = ⊤)
    (hp : ∀ᵉ (x ∈ M') (y ∈ N'), p x y ∈ (algebraMap K L).range) :
    finrank K M' = finrank L M := by
  obtain ⟨n, b, b', hb⟩ := exists_basis_basis_of_span_eq_top_of_mem_algebraMap p M' N' hM hN hp
  rw [finrank_eq_card_basis b, finrank_eq_card_basis b']

variable {M' N' : Type*}
  [AddCommGroup M'] [AddCommGroup N'] [Module K M'] [Module K N'] [IsScalarTower K L N]
  (i : M' →ₗ[K] M) (j : N' →ₗ[K] N) (hi : Injective i) (hj : Injective j)

include hi hj in
/-- An auxiliary definition used only to simplify the construction of the more general definition
`PerfectPairing.restrictScalarsField`. -/
/-
**LinearMap.restrictScalars_field_aux** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary definition used only to simplify the construction of the more gener
al definition
`PerfectPairing.restrictScalarsField`.
-/
private lemma restrictScalars_field_aux
    (hM : span L (LinearMap.range i : Set M) = ⊤)
    (hN : span L (LinearMap.range j : Set N) = ⊤)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap K L).range) :
    (LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap K L)
      (FaithfulSMul.algebraMap_injective K L) p hp).IsPerfPair := by
  suffices FiniteDimensional K M' from .of_injective (p.restrictScalars_injective_aux i j hi hN hp)
    (p.flip.restrictScalars_injective_aux j i hj hM (fun m n ↦ hp n m))
  obtain ⟨n, -, b', -⟩ := p.exists_basis_basis_of_span_eq_top_of_mem_algebraMap _ _ hM hN <| by
    rintro - ⟨m, rfl⟩ - ⟨n, rfl⟩
    exact hp m n
  have : FiniteDimensional K (LinearMap.range i) := b'.finiteDimensional_of_finite
  exact Finite.equiv (LinearEquiv.ofInjective i hi).symm

set_option backward.isDefEq.respectTransparency false in
include hi hj in
/-- Simultaneously restrict both the domains and scalars of a perfect pairing with coefficients in a
field. -/
/-
**LinearMap.IsPerfPair.restrictScalars_of_field** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap.IsPerfPair`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Fiel
d K] [inst_1 : Field L] [inst_2 : Algebra K L]   [inst_3 : AddCommGroup M] [inst
_4 : AddCommGroup N] [inst_5 : _root_.Module L M] [inst_6 : _root_.Module L N]  
 [inst_7 : _root_.Module K M] [inst_8 : _root_.Module K N] [inst_9 : IsScalarTow
er K L M] (p : M →ₗ[L] N →ₗ[L] L)   [inst_10 : p.IsPerfPair] {M' : Type u_5} {N'
 : Type u_6} [inst_11 : AddCommGroup M'] [inst_12 : AddCommGroup N']   [inst_13 
: _root_.Module K M'] [inst_14 : _root_.Module K N'] [inst_15 : IsScalarTower K 
L N] (i : M' →ₗ[K] M)   (j : N' →ₗ[K] N),   Function.Injective ⇑i →     Function
.Injective ⇑j →       p.IsPerfectCompl (Submodule.span L ↑i.range) (Submodule.sp
an L ↑j.range) →         ∀ (hp : ∀ (m : M') (n : N'), (p (i m)) (j n) ∈ (algebra
Map K L).range),           (i.restrictScalarsRange₂ j (Algebra.linearMap K L) ⋯ 
p hp).IsPerfPair
参数：p : M →ₗ[L] N →ₗ[L] L；i : M' →ₗ[K] M；j : N' →ₗ[K] N；Submodule.span L ↑i.range
；Submodule.span L ↑j.range；hp : ∀ (m : M') (n : N'), (p (i m)) (j n) ∈ (algebraM
ap K L).range；i.restrictScalarsRange₂ j (Algebra.linearMap K L) ⋯ p hp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsPerfPair.restrict`：∀ {R : Type u_1} {M : Type u_2} {N : Type
 u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R 
M] [inst_3 : AddCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearMap.IsPerfectCompl.congr_simp`：∀ {R : Type u_1} {M : Type u_2} {N 
: Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Mod
ule R M] [inst_3 : AddCom…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `_private.Mathlib.LinearAlgebra.PerfectPairing.Restrict.0.LinearMap.restr
ictScalars_field_aux`：∀ {K : Type u_1} {L : Type u_2} {M : Type u_3} {N : Type u
_4} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   [inst_3 : AddCo
mm…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `Submodule.injective_inclusionSpan`：injective_inclusionSpan : Injective (
p.inclusionSpan S)
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_comp_of_range_eq_top`：range_comp_of_range_eq_top [RingHo
mSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] {f : M ->ₛₗ[τ₁₂
] M₂} (g : M₂ ->ₛₗ[τ₂₃] M₃…
· 使用定理 `LinearMap.range_rangeRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Typ
e u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
· 使用引理 `Submodule.span_range_inclusionSpan`：span_range_inclusionSpan : span S (r
ange <| p.inclusionSpan S) = ⊤
· 使用定理 `LinearMap.BilinMap.apply_apply_mem_of_mem_span`：∀ {R : Type u_9} {M : Ty
pe u_10} {N : Type u_11} {P : Type u_12} [inst : CommSemiring R] [inst_1 : AddCo
mmMonoid M]   [inst_2 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.restrictScalarsₗ_apply`：∀ (R : Type u_14) (S : Type u_15) (M :
 Type u_16) (N : Type u_17) [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 
: AddCommMonoid M] [in…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
Simultaneously restrict both the domains and scalars of a perfect pairing with c
oefficients in a
field.
-/
lemma IsPerfPair.restrictScalars_of_field
    (hij : p.IsPerfectCompl (span L <| LinearMap.range i) (span L <| LinearMap.range j))
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap K L).range) :
    (LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap K L)
      (FaithfulSMul.algebraMap_injective K L) p hp).IsPerfPair := by
  have : (p.compl₁₂ (span L <| .range i).subtype (span L <| .range j).subtype).IsPerfPair :=
    .restrict _ _ _ (by simp) (by simp) (by simpa)
  exact restrictScalars_field_aux
    (p.compl₁₂ (span L <| .range i).subtype (span L <| .range j).subtype)
    ((LinearMap.range i).inclusionSpan L ∘ₗ i.rangeRestrict)
    ((LinearMap.range j).inclusionSpan L ∘ₗ j.rangeRestrict)
    (((LinearMap.range i).injective_inclusionSpan L).comp (by simpa))
    (((LinearMap.range j).injective_inclusionSpan L).comp (by simpa))
    (by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_rangeRestrict _)]
        exact (LinearMap.range i).span_range_inclusionSpan L)
    (by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_rangeRestrict _)]
        exact (LinearMap.range j).span_range_inclusionSpan L)
    fun x y ↦ LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (LinearMap.range <| Algebra.linearMap K L) (range i) (range j)
      ((LinearMap.restrictScalarsₗ K L _ _ _).comp (p.restrictScalars K))
      (by simpa) (i x) (j y) (subset_span <| by simp) (subset_span <| by simp)

omit [p.IsPerfPair] in
/-
**LinearMap.restrictScalarsField_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Fiel
d K] [inst_1 : Field L] [inst_2 : Algebra K L]   [inst_3 : AddCommGroup M] [inst
_4 : AddCommGroup N] [inst_5 : _root_.Module L M] [inst_6 : _root_.Module L N]  
 [inst_7 : _root_.Module K M] [inst_8 : _root_.Module K N] [inst_9 : IsScalarTow
er K L M] (p : M →ₗ[L] N →ₗ[L] L)   {M' : Type u_5} {N' : Type u_6} [inst_10 : A
ddCommGroup M'] [inst_11 : AddCommGroup N'] [inst_12 : _root_.Module K M']   [in
st_13 : _root_.Module K N'] [inst_14 : IsScalarTower K L N] (i : M' →ₗ[K] M) (j 
: N' →ₗ[K] N)   (hp : ∀ (m : M') (n : N'), (p (i m)) (j n) ∈ (algebraMap K L).ra
nge) (x : M') (y : N'),   (algebraMap K L) (((i.restrictScalarsRange₂ j (Algebra
.linearMap K L) ⋯ p hp) x) y) = (p (i x)) (j y)
参数：p : M →ₗ[L] N →ₗ[L] L；i : M' →ₗ[K] M；j : N' →ₗ[K] N；hp : ∀ (m : M') (n : N'),
 (p (i m)) (j n) ∈ (algebraMap K L).range；x : M'；y : N'；algebraMap K L；((i.restr
ictScalarsRange₂ j (Algebra.linearMap K L) ⋯ p hp) x) y；p (i x)；j y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.restrictScalarsRange₂_apply`：∀ {R : Type u_1} {S : Type u_2} {
M : Type u_3} {N : Type u_4} {P : Type u_5} {M' : Type u_6} {N' : Type u_7}   {P
' : Type u_8} [inst : CommS…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
@[simp] lemma restrictScalarsField_apply_apply (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap K L).range)
    (x : M') (y : N') :
    algebraMap K L (LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap K L)
      (FaithfulSMul.algebraMap_injective K L) p hp x y) = p (i x) (j y) :=
  LinearMap.restrictScalarsRange₂_apply i j (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) p hp x y

end Field

end LinearMap

