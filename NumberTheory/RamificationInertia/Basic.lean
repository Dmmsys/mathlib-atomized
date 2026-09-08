/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Ramification index and inertia degree

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `Ideal.ramificationIdx f p P` is the multiplicity of `P` in `map f p`,
and the **inertia degree** `Ideal.inertiaDeg f p P` is the degree of the field extension
`(S / P) : (R / p)`.

## Main results

The main theorem `Ideal.sum_ramification_inertia` states that for all coprime `P` lying over `p`,
`Σ P, ramification_idx f p P * inertia_deg f p P` equals the degree of the field extension
`Frac(S) : Frac(R)`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`

We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `e` stands for the ramification index and `f` for the inertia degree of `P` over `p`,
leaving `p` and `P` implicit.

-/

deprecated_module "Use RingTheory.RamificationInertia.Basic" (since := "2026-07-01")

@[expose] public section


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section FinrankQuotientMap

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [Algebra R K]
variable {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L]
variable {V V' V'' : Type*}
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [AddCommGroup V'] [Module R V'] [Module S V'] [IsScalarTower R S V']
variable [AddCommGroup V''] [Module R V'']
variable (K)

open scoped Matrix

variable {K} in
/-- If `b` mod `p` spans `S/p` as `R/p`-space, then `b` itself spans `Frac(S)` as `K`-space.

Here,
* `p` is an ideal of `R` such that `R / p` is nontrivial
* `K` is a field that has an embedding of `R` (in particular we can take `K = Frac(R)`)
* `L` is a field extension of `K`
* `S` is the integral closure of `R` in `L`

More precisely, we avoid quotients in this statement and instead require that `b ∪ pS` spans `S`.
-/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.FinrankQuotientMap.span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.FinrankQ
uotientMap`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   {K : Type u_1} [inst_3 : Field K] [inst_4 : A
lgebra R K] {L : Type u_2} [inst_5 : Field L] [inst_6 : Algebra S L]   [IsFracti
onRing S L] [IsDomain R] [IsDomain S] [inst_10 : Algebra K L] [Module.Finite R S
] [inst_12 : Algebra R L]   [IsScalarTower R S L] [IsScalarTower R K L] [Algebra
.IsAlgebraic R S] [Module.IsTorsionFree R K],   p ≠ ⊤ →     ∀ (b : Set S),      
 Submodule.span R b ⊔ Submodule.restrictScalars R (Ideal.map (algebraMap R S) p)
 = ⊤ →         Submodule.span K (⇑(algebraMap S L) '' b) = ⊤
参数：p : Ideal R；b : Set S；Ideal.map (algebraMap R S) p；⇑(algebraMap S L) '' b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Module.Finite.exists_fin`：exists_fin [Module.Finite R M] : exists (n : N
at) (s : Fin n -> M), span R (range s) = ⊤
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.map_mkQ_eq_top`：map_mkQ_eq_top : map p.mkQ p' = ⊤ ↔ p ⊔ p' = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_ideal_smul_span_iff_exists_sum`：mem_ideal_smul_span_iff_ex
ists_sum {ι : Type*} (f : ι -> M) (x : M) : x in I • span R (Set.range f) ↔ exis
ts (a : ι ->₀ R) (_ : forall i, a …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
（共 93 条，此处仅展示前 30 条）

--- 原说明 ---
If `b` mod `p` spans `S/p` as `R/p`-space, then `b` itself spans `Frac(S)` as `K
`-space.

Here,
* `p` is an ideal of `R` such that `R / p` is nontrivial
* `K` is a field that has an embedding of `R` (in particular we can take `K = Fr
ac(R)`)
* `L` is a field extension of `K`
* `S` is the integral closure of `R` in `L`

More precisely, we avoid quotients in this statement and instead require that `b
 ∪ pS` spans `S`.
-/
theorem FinrankQuotientMap.span_eq_top [IsDomain R] [IsDomain S] [Algebra K L] [Module.Finite R S]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [Algebra.IsAlgebraic R S]
    [IsTorsionFree R K] (hp : p ≠ ⊤) (b : Set S)
    (hb' : Submodule.span R b ⊔ (p.map (algebraMap R S)).restrictScalars R = ⊤) :
    Submodule.span K (algebraMap S L '' b) = ⊤ := by
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (FaithfulSMul.algebraMap_injective R K)
  -- Let `M` be the `R`-module spanned by the proposed basis elements.
  let M : Submodule R S := Submodule.span R b
  -- Then `S / M` is generated by some finite set of `n` vectors `a`.
  obtain ⟨n, a, ha⟩ := @Module.Finite.exists_fin R (S ⧸ M) _ _ _ _
  -- Because the image of `p` in `S / M` is `⊤`,
  have smul_top_eq : p • (⊤ : Submodule R (S ⧸ M)) = ⊤ := by
    calc
      p • ⊤ = Submodule.map M.mkQ (p • ⊤) := by
        rw [Submodule.map_smul'', Submodule.map_top, M.range_mkQ]
      _ = ⊤ := by rw [Ideal.smul_top_eq_map, (Submodule.map_mkQ_eq_top M _).mpr hb']
  -- we can write the elements of `a` as `p`-linear combinations of other elements of `a`.
  have exists_sum : ∀ x : S ⧸ M, ∃ a' : Fin n → R, (∀ i, a' i ∈ p) ∧ ∑ i, a' i • a i = x := by
    intro x
    obtain ⟨a'', ha'', hx⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum p a x).1
      (by { rw [ha, smul_top_eq]; exact Submodule.mem_top } :
        x ∈ p • Submodule.span R (Set.range a))
    · refine ⟨fun i => a'' i, fun i => ha'' _, ?_⟩
      rw [← hx, Finsupp.sum_fintype]
      exact fun _ => zero_smul _ _
  choose A' hA'p hA' using fun i => exists_sum (a i)
  -- This gives us a(n invertible) matrix `A` such that `det A ∈ (M = span R b)`,
  let A : Matrix (Fin n) (Fin n) R := Matrix.of A' - 1
  let B := A.adjugate
  have A_smul : ∀ i, ∑ j, A i j • a j = 0 := by
    intros
    simp [A, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, sub_smul,
      Finset.sum_sub_distrib, hA', sub_self]
  -- since `span S {det A} / M = 0`.
  have d_smul : ∀ i, A.det • a i = 0 := by
    intro i
    calc
      A.det • a i = ∑ j, (B * A) i j • a j := ?_
      _ = ∑ k, B i k • ∑ j, A k j • a j := ?_
      _ = 0 := Finset.sum_eq_zero fun k _ => ?_
    · simp only [B, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_true,
        mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]
    · simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
    · rw [A_smul, smul_zero]
  -- In the rings of integers we have the desired inclusion.
  have span_d : (Submodule.span S ({algebraMap R S A.det} : Set S)).restrictScalars R ≤ M := by
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [smul_eq_mul, mul_comm, ← Algebra.smul_def] at hx ⊢
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    obtain ⟨a', _, quot_x_eq⟩ := exists_sum (Submodule.Quotient.mk x')
    rw [← quot_x_eq, Finset.smul_sum]
    conv =>
      lhs; congr; next => skip
      intro x; rw [smul_comm A.det, d_smul, smul_zero]
    exact Finset.sum_const_zero
  refine top_le_iff.mp
      (calc
        ⊤ = (Ideal.span {algebraMap R L A.det}).restrictScalars K := ?_
        _ ≤ Submodule.span K (algebraMap S L '' b) := ?_)
  -- Because `det A ≠ 0`, we have `span L {det A} = ⊤`.
  · rw [eq_comm, Submodule.restrictScalars_eq_top_iff, Ideal.span_singleton_eq_top]
    refine IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R L) hRL).mpr ?_)
    refine ne_zero_of_map («f» := Ideal.Quotient.mk p) ?_
    have := Ideal.Quotient.nontrivial_iff.mpr hp
    calc
      Ideal.Quotient.mk p A.det = Matrix.det ((Ideal.Quotient.mk p).mapMatrix A) := by
        rw [RingHom.map_det]
      _ = Matrix.det ((Ideal.Quotient.mk p).mapMatrix (Matrix.of A' - 1)) := rfl
      _ = Matrix.det fun i j =>
          (Ideal.Quotient.mk p) (A' i j) - (1 : Matrix (Fin n) (Fin n) (R ⧸ p)) i j := ?_
      _ = Matrix.det (-1 : Matrix (Fin n) (Fin n) (R ⧸ p)) := ?_
      _ = (-1 : R ⧸ p) ^ n := by rw [Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_one]
      _ ≠ 0 := IsUnit.ne_zero (isUnit_one.neg.pow _)
    · refine congr_arg Matrix.det (Matrix.ext fun i j => ?_)
      rw [map_sub, RingHom.mapMatrix_apply, map_one]
      simp
    · refine congr_arg Matrix.det (Matrix.ext fun i j => ?_)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hA'p i j), zero_sub, Matrix.neg_apply]
  -- And we conclude `L = span L {det A} ≤ span K b`, so `span K b` spans everything.
  · intro x hx
    rw [Submodule.restrictScalars_mem, IsScalarTower.algebraMap_apply R S L] at hx
    exact IsFractionRing.ideal_span_singleton_map_subset R hRL span_d hx

variable [hRK : IsFractionRing R K]

/-- Let `V` be a vector space over `K = Frac(R)`, `S / R` a ring extension
and `V'` a module over `S`. If `b`, in the intersection `V''` of `V` and `V'`,
is linear independent over `S` in `V'`, then it is linear independent over `R` in `V`.

The statement we prove is actually slightly more general:
* it suffices that the inclusion `algebraMap R S : R → S` is nontrivial
* the function `f' : V'' → V'` doesn't need to be injective
-/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial** 是 Mathlib 中的一个定理，位于
命名空间 `Ideal.FinrankQuotientMap`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (K : Type u_1)   [inst_3 : Field K] [inst_4 : Algebra R K] {V
 : Type u_3} {V' : Type u_4} {V'' : Type u_5} [inst_5 : AddCommGroup V]   [inst_
6 : _root_.Module R V] [inst_7 : _root_.Module K V] [IsScalarTower R K V] [inst_
9 : AddCommGroup V']   [inst_10 : _root_.Module R V'] [inst_11 : _root_.Module S
 V'] [IsScalarTower R S V'] [inst_13 : AddCommGroup V'']   [inst_14 : _root_.Mod
ule R V''] [hRK : IsFractionRing R K] [IsDedekindDomain R],   RingHom.ker (algeb
raMap R S) ≠ ⊤ →     ∀ (F : V'' →ₗ[R] V),       Function.Injective ⇑F →         
∀ (f' : V'' →ₗ[R] V') {ι : Type u_6} {b : ι → V''}, LinearIndependent S (⇑f' ∘ b
) → LinearIndependent K (⇑F ∘ b)
参数：K : Type u_1；algebraMap R S；F : V'' →ₗ[R] V；f' : V'' →ₗ[R] V'；⇑f' ∘ b；⇑F ∘ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Ideal.exist_integer_multiples_notMem`：exist_integer_multiples_notMem {J 
: Ideal A} (hJ : J != ⊤) {ι : Type*} (s : Finset ι) (f : ι -> K) {j} (hjs : j in
 s) (hjf : f j != 0) : exi…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.map_eq_zero_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8
} {M₃ : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddComm
Monoid M] [inst…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Let `V` be a vector space over `K = Frac(R)`, `S / R` a ring extension
and `V'` a module over `S`. If `b`, in the intersection `V''` of `V` and `V'`,
is linear independent over `S` in `V'`, then it is linear independent over `R` i
n `V`.

The statement we prove is actually slightly more general:
* it suffices that the inclusion `algebraMap R S : R → S` is nontrivial
* the function `f' : V'' → V'` doesn't need to be injective
-/
theorem FinrankQuotientMap.linearIndependent_of_nontrivial [IsDedekindDomain R]
    (hRS : RingHom.ker (algebraMap R S) ≠ ⊤) (F : V'' →ₗ[R] V) (hf : Function.Injective F)
    (f' : V'' →ₗ[R] V') {ι : Type*} {b : ι → V''} (hb' : LinearIndependent S (f' ∘ b)) :
    LinearIndependent K (F ∘ b) := by
  contrapose hb' with hb
  -- Informally, if we have a nontrivial linear dependence with coefficients `g` in `K`,
  -- then we can find a linear dependence with coefficients `I.Quotient.mk g'` in `R/I`,
  -- where `I = ker (algebraMap R S)`.
  -- We make use of the same principle but stay in `R` everywhere.
  simp only [linearIndependent_iff', not_forall] at hb ⊢
  obtain ⟨s, g, eq, j', hj's, hj'g⟩ := hb
  use s
  obtain ⟨a, hag, j, hjs, hgI⟩ := Ideal.exist_integer_multiples_notMem hRS s g hj's hj'g
  choose g'' hg'' using hag
  let := Classical.propDecidable
  let g' i := if h : i ∈ s then g'' i h else 0
  have hg' : ∀ i ∈ s, algebraMap _ _ (g' i) = a * g i := by
    intro i hi; exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi)
  -- Because `R/I` is nontrivial, we can lift `g` to a nontrivial linear dependence in `S`.
  have hgI : algebraMap R S (g' j) ≠ 0 := by
    simp only [FractionalIdeal.mem_coeIdeal, not_exists, not_and'] at hgI
    exact hgI _ (hg' j hjs)
  refine ⟨fun i => algebraMap R S (g' i), ?_, j, hjs, hgI⟩
  have eq : F (∑ i ∈ s, g' i • b i) = 0 := by
    rw [map_sum, ← smul_zero a, ← eq, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [map_smul, ← IsScalarTower.algebraMap_smul K, hg' i hi, ← smul_assoc,
      smul_eq_mul, Function.comp_apply]
  simp only [IsScalarTower.algebraMap_smul, ← map_smul, ← map_sum,
    (F.map_eq_zero_iff hf).mp eq, map_zero, (· ∘ ·)]

variable (L)

/-- If `p` is a maximal ideal of `R`, and `S` is the integral closure of `R` in `L`,
then the dimension `[S/pS : R/p]` is equal to `[Frac(S) : Frac(R)]`. -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.finrank_quotient_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：finrank_quotient_map [IsDomain S] [IsDedekindDomain R] [Algebra K L] [Alge
bra R L] [IsScalarTower R K L] [IsScalarTower R S L] [hp : p.IsMaximal] [Module.
Finite R S] : finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial`：∀ {R : Type u}
 [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (
K : Type u_1)   [inst_3 : Field K] [inst_4 : A…
· 使用定理 `Ideal.Quotient.tower_quotient_map_quotient`：∀ {R : Type u_1} [inst : Com
mRing R] {S : Type u_2} [inst_1 : CommRing S] {p : Ideal R} [inst_2 : Algebra R 
S],   IsScalarTower R (R ⧸ p) (S…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.algebraMap_eq`：∀ {R : Type u_5} [inst : CommRing R] (I : 
Ideal R), algebraMap R (R ⧸ I) = Ideal.Quotient.mk I
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Ideal.FinrankQuotientMap.span_eq_top`：∀ {R : Type u} [inst : CommRing R]
 {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   {K : 
Type u_1} [inst_3 : Field …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
If `p` is a maximal ideal of `R`, and `S` is the integral closure of `R` in `L`,
then the dimension `[S/pS : R/p]` is equal to `[Frac(S) : Frac(R)]`.
-/
theorem finrank_quotient_map [IsDomain S] [IsDedekindDomain R] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    [hp : p.IsMaximal] [Module.Finite R S] :
    finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L := by
  -- Choose an arbitrary basis `b` for `[S/pS : R/p]`.
  -- We'll use the previous results to turn it into a basis on `[Frac(S) : Frac(R)]`.
  let ι := Module.Free.ChooseBasisIndex (R ⧸ p) (S ⧸ map (algebraMap R S) p)
  let b : Basis ι (R ⧸ p) (S ⧸ map (algebraMap R S) p) := Module.Free.chooseBasis _ _
  -- Namely, choose a representative `b' i : S` for each `b i : S / pS`.
  let b' : ι → S := fun i => (Ideal.Quotient.mk_surjective (b i)).choose
  have b_eq_b' : ⇑b = (Submodule.mkQ (map (algebraMap R S) p)).restrictScalars R ∘ b' :=
    funext fun i => (Ideal.Quotient.mk_surjective (b i)).choose_spec.symm
  -- We claim `b'` is a basis for `Frac(S)` over `Frac(R)` because it is linear independent
  -- and spans the whole of `Frac(S)`.
  let b'' : ι → L := algebraMap S L ∘ b'
  have b''_li : LinearIndependent K b'' := ?_
  · have b''_sp : Submodule.span K (Set.range b'') = ⊤ := ?_
    -- Since the two bases have the same index set, the spaces have the same dimension.
    · let c : Basis ι K L := Basis.mk b''_li b''_sp.ge
      rw [finrank_eq_card_basis b, finrank_eq_card_basis c]
    -- It remains to show that the basis is indeed linear independent and spans the whole space.
    · rw [Set.range_comp]
      refine FinrankQuotientMap.span_eq_top p hp.ne_top _ (top_le_iff.mp ?_)
      -- The nicest way to show `S ≤ span b' ⊔ pS` is by reducing both sides modulo pS.
      -- However, this would imply distinguishing between `pS` as `S`-ideal,
      -- and `pS` as `R`-submodule, since they have different (non-defeq) quotients.
      -- Instead we'll lift `x mod pS ∈ span b` to `y ∈ span b'` for some `y - x ∈ pS`.
      intro x _
      have mem_span_b : ((Submodule.mkQ (map (algebraMap R S) p)) x : S ⧸ map (algebraMap R S) p) ∈
          Submodule.span (R ⧸ p) (Set.range b) := b.mem_span _
      rw [← @Submodule.restrictScalars_mem R,
        Submodule.restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective, b_eq_b',
        Set.range_comp, ← Submodule.map_span] at mem_span_b
      obtain ⟨y, y_mem, y_eq⟩ := Submodule.mem_map.mp mem_span_b
      suffices y + -(y - x) ∈ _ by simpa
      rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at y_eq
      exact add_mem (Submodule.mem_sup_left y_mem) (neg_mem <| Submodule.mem_sup_right y_eq)
  · have := b.linearIndependent; rw [b_eq_b'] at this
    convert!
      FinrankQuotientMap.linearIndependent_of_nontrivial K _
        ((Algebra.linearMap S L).restrictScalars R) _ ((Submodule.mkQ _).restrictScalars R) this
    · rw [Quotient.algebraMap_eq, Ideal.mk_ker]
      exact hp.ne_top
    · exact IsFractionRing.injective S L

end FinrankQuotientMap

section FactLeComap

local notation "e" => ramificationIdx' p P

/-- `R / p` has a canonical map to `S / (P ^ e)`, where `e` is the ramification index
of `P` over `p`. -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Quotient.algebraQuotientPowRamificationIdx** 是 Mathlib 中的一个定义，位于命名空间 `Id
eal.Quotient`。
形式化陈述：{R : Type u} →   [inst : CommRing R] →     {S : Type v} →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] → (p : Ideal R) → (P : Ideal S) → A
lgebra (R ⧸ p) (S ⧸ P ^ p.ramificationIdx' P)
参数：p : Ideal R；P : Ideal S；R ⧸ p；S ⧸ P ^ p.ramificationIdx' P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R / p` has a canonical map to `S / (P ^ e)`, where `e` is the ramification inde
x
of `P` over `p`.
-/
noncomputable instance Quotient.algebraQuotientPowRamificationIdx : Algebra (R ⧸ p) (S ⧸ P ^ e) :=
  Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp le_pow_ramificationIdx')

@[simp, deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Quotient.algebraMap_quotient_pow_ramificationIdx** 是 Mathlib 中的一个定理，位于命名
空间 `Ideal.Quotient`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   (x : R),   (algebraMap (R ⧸ p) 
(S ⧸ P ^ p.ramificationIdx' P)) ((Ideal.Quotient.mk p) x) =     (Ideal.Quotient.
mk (P ^ p.ramificationIdx' P)) ((algebraMap R S) x)
参数：p : Ideal R；P : Ideal S；x : R；algebraMap (R ⧸ p) (S ⧸ P ^ p.ramificationIdx' 
P)；(Ideal.Quotient.mk p) x；Ideal.Quotient.mk (P ^ p.ramificationIdx' P)；(algebra
Map R S) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem Quotient.algebraMap_quotient_pow_ramificationIdx (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk (P ^ e) (f x) := rfl

/-- If `P` lies over `p`, then `R / p` has a canonical map to `S / P`.

This can't be an instance since the map `f : R → S` is generally not inferable.
-/
@[instance_reducible,
  deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero** 是 Mathlib 中的一个定义，位于命名空
间 `Ideal.Quotient`。
形式化陈述：{R : Type u} →   [inst : CommRing R] →     {S : Type v} →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           (p : Ideal R) → (P : Id
eal S) → [hfp : NeZero (p.ramificationIdx' P)] → Algebra (R ⧸ p) (S ⧸ P)
参数：p : Ideal R；P : Ideal S；p.ramificationIdx' P；R ⧸ p；S ⧸ P。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
def Quotient.algebraQuotientOfRamificationIdxNeZero [hfp : NeZero e] :
    Algebra (R ⧸ p) (S ⧸ P) :=
  Quotient.algebraQuotientOfLEComap (le_comap_of_ramificationIdx'_ne_zero hfp.out)

attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

@[simp, deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Quotient.algebraMap_quotient_of_ramificationIdx_neZero** 是 Mathlib 中的一个定
理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   [inst_3 : NeZero (p.ramificatio
nIdx' P)] (x : R),   (algebraMap (R ⧸ p) (S ⧸ P)) ((Ideal.Quotient.mk p) x) = (I
deal.Quotient.mk P) ((algebraMap R S) x)
参数：p : Ideal R；P : Ideal S；p.ramificationIdx' P；x : R；algebraMap (R ⧸ p) (S ⧸ P)
；(Ideal.Quotient.mk p) x；Ideal.Quotient.mk P；(algebraMap R S) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem Quotient.algebraMap_quotient_of_ramificationIdx_neZero
    [NeZero e] (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk P (f x) := rfl

/-- The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`. -/
@[simps, deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.powQuotSuccInclusion** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：powQuotSuccInclusion (i : Nat) : Ideal.map (Ideal.Quotient.mk (P ^ e)) (P 
^ (i + 1)) ->ₗ[R ⧸ p] Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i) where toFun 
x
参数：i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`.
-/
noncomputable def powQuotSuccInclusion (i : ℕ) :
    Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1)) →ₗ[R ⧸ p]
    Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i) where
  toFun x := ⟨x, Ideal.map_mono (Ideal.pow_le_pow_right i.le_succ) x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.powQuotSuccInclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：powQuotSuccInclusion_injective (i : Nat) : Function.Injective (powQuotSucc
Inclusion p P i)
参数：i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem powQuotSuccInclusion_injective (i : ℕ) :
    Function.Injective (powQuotSuccInclusion p P i) := by
  rintro ⟨_, _⟩ ⟨_, _⟩ h
  rwa [Subtype.ext_iff] at h ⊢

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`.
See `quotientToQuotientRangePowQuotSucc` for this as a linear map,
and `quotientRangePowQuotSuccInclusionEquiv` for this as a linear equivalence.
-/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.quotientToQuotientRangePowQuotSuccAux** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientToQuotientRangePowQuotSuccAux {i : Nat} {a : S} (a_mem : a in P ^ 
i) : S ⧸ P -> (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuot
SuccInclusion p P i)
参数：a_mem : a in P ^ i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
`S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`
.
See `quotientToQuotientRangePowQuotSucc` for this as a linear map,
and `quotientRangePowQuotSuccInclusionEquiv` for this as a linear equivalence.
-/
noncomputable def quotientToQuotientRangePowQuotSuccAux {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →
      (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i) :=
  Quotient.map' (fun x : S => ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩)
    fun x y h => by
    rw [Submodule.quotientRel_def] at h ⊢
    simp only [map_mul, LinearMap.mem_range]
    refine ⟨⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul a_mem h)⟩, ?_⟩
    ext
    rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Submodule.coe_sub, Subtype.coe_mk,
      Subtype.coe_mk, map_mul, map_sub, mul_sub]

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.quotientToQuotientRangePowQuotSuccAux_mk** 是 Mathlib 中的一个定理，位于命名空间 `Idea
l`。
形式化陈述：quotientToQuotientRangePowQuotSuccAux_mk {i : Nat} {a : S} (a_mem : a in P
 ^ i) (x : S) : quotientToQuotientRangePowQuotSuccAux p P a_mem (Submodule.Quoti
ent.mk x) = Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_righ
t x _ a_mem)⟩
参数：a_mem : a in P ^ i；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Quotient.map'_mk''`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} {s₂ 
: Setoid β} (f : α → β) (h : ∀ (a b : α), s₁ a b → s₂ (f a) (f b))   (x : α), Qu
otient.m…
-/
theorem quotientToQuotientRangePowQuotSuccAux_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSuccAux p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩ := by
  apply Quotient.map'_mk''

section
variable [hfp : NeZero (ramificationIdx' p P)]

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`. -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.quotientToQuotientRangePowQuotSucc** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotientToQuotientRangePowQuotSucc {i : Nat} {a : S} (a_mem : a in P ^ i) 
: S ⧸ P ->ₗ[R ⧸ p] (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (po
wQuotSuccInclusion p P i) where toFun
参数：a_mem : a in P ^ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`
.
-/
noncomputable def quotientToQuotientRangePowQuotSucc
    {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →ₗ[R ⧸ p]
      (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i) where
  toFun := quotientToQuotientRangePowQuotSuccAux p P a_mem
  map_add' x y := by
    induction x, y using Quotient.inductionOn₂' with | _ x y
    simp only [Submodule.Quotient.mk''_eq_mk, ← Submodule.Quotient.mk_add,
      quotientToQuotientRangePowQuotSuccAux_mk, mul_add, map_add, map_mul, AddMemClass.mk_add_mk]
  map_smul' x y := by
    induction x, y using Quotient.inductionOn₂' with | _ x y
    simp only [Submodule.Quotient.mk''_eq_mk, RingHom.id_apply,
      quotientToQuotientRangePowQuotSuccAux_mk]
    refine congr_arg Submodule.Quotient.mk ?_
    ext
    simp only [map_mul, Quotient.mk_eq_mk, Submodule.coe_smul_of_tower,
      Algebra.smul_def, Quotient.algebraMap_quotient_pow_ramificationIdx]
    ring

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.quotientToQuotientRangePowQuotSucc_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotientToQuotientRangePowQuotSucc_mk {i : Nat} {a : S} (a_mem : a in P ^ 
i) (x : S) : quotientToQuotientRangePowQuotSucc p P a_mem (Submodule.Quotient.mk
 x) = Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ 
a_mem)⟩
参数：a_mem : a in P ^ i；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.quotientToQuotientRangePowQuotSuccAux_mk`：quotientToQuotientRangeP
owQuotSuccAux_mk {i : Nat} {a : S} (a_mem : a in P ^ i) (x : S) : quotientToQuot
ientRangePowQuotSuccAux p P a_mem (S…
-/
theorem quotientToQuotientRangePowQuotSucc_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSucc p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩ :=
  quotientToQuotientRangePowQuotSuccAux_mk p P a_mem x

set_option backward.isDefEq.respectTransparency.types false in
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.quotientToQuotientRangePowQuotSucc_injective** 是 Mathlib 中的一个定理，位于命名空间 `
Ideal`。
形式化陈述：quotientToQuotientRangePowQuotSucc_injective [IsDedekindDomain S] [P.IsPri
me] {i : Nat} (hi : i < e) {a : S} (a_mem : a in P ^ i) (a_notMem : a ∉ P ^ (i +
 1)) : Function.Injective (quotientToQuotientRangePowQuotSucc p P a_mem)
参数：hi : i < e；a_mem : a in P ^ i；a_notMem : a ∉ P ^ (i + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.quotientToQuotientRangePowQuotSucc_mk`：quotientToQuotientRangePowQ
uotSucc_mk {i : Nat} {a : S} (a_mem : a in P ^ i) (x : S) : quotientToQuotientRa
ngePowQuotSucc p P a_mem (Submodu…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.coe_sub`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   (x y : ↥p)
, ↑(x -…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.IsPrime.mem_pow_mul`：∀ {R : Type u_1} [inst : CommRing R] [IsDedek
indDomain R] (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ},   a * b ∈ I ^ n →
 a ∈ I ^ n ∨ b …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.sub_mem_iff_right`：sub_mem_iff_right (hx : x in p) : x - y in 
p ↔ y in p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Ideal.mem_quotient_iff_mem_sup`：mem_quotient_iff_mem_sup {I J : Ideal R}
 [I.IsTwoSided] {x : R} : Quotient.mk I x in J.map (Quotient.mk I) ↔ x in J ⊔ I
· 使用定理 `Ideal.Quotient.mk_eq_mk`：mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R
 ⧸ I) = mk I x
· 使用定理 `Submodule.Quotient.quot_mk_eq_mk`：quot_mk_eq_mk {p : Submodule R M} (x :
 M) : (Quot.mk _ x : M ⧸ p) = mk x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Ideal.powQuotSuccInclusion_apply_coe`：∀ {R : Type u} [inst : CommRing R]
 {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Id
eal S)   (i : ℕ) (x : ↥(Id…
-/
theorem quotientToQuotientRangePowQuotSucc_injective [IsDedekindDomain S] [P.IsPrime]
    {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i) (a_notMem : a ∉ P ^ (i + 1)) :
    Function.Injective (quotientToQuotientRangePowQuotSucc p P a_mem) := fun x =>
  Quotient.inductionOn' x fun x y =>
    Quotient.inductionOn' y fun y h => by
      have Pe_le_Pi1 : P ^ e ≤ P ^ (i + 1) := Ideal.pow_le_pow_right hi
      simp only [Submodule.Quotient.mk''_eq_mk, quotientToQuotientRangePowQuotSucc_mk,
        Submodule.Quotient.eq, LinearMap.mem_range, Subtype.ext_iff,
        Submodule.coe_sub] at h ⊢
      rcases h with ⟨⟨⟨z⟩, hz⟩, h⟩
      rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
        sup_eq_left.mpr Pe_le_Pi1] at hz
      rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Submodule.Quotient.quot_mk_eq_mk,
        Ideal.Quotient.mk_eq_mk, ← map_sub, Ideal.Quotient.eq, ← mul_sub] at h
      exact
        (Ideal.IsPrime.mem_pow_mul _
              ((Submodule.sub_mem_iff_right _ hz).mp (Pe_le_Pi1 h))).resolve_left
          a_notMem

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.quotientToQuotientRangePowQuotSucc_surjective** 是 Mathlib 中的一个定理，位于命名空间 
`Ideal`。
形式化陈述：quotientToQuotientRangePowQuotSucc_surjective [IsDedekindDomain S] (hP0 : 
P != ⊥) [hP : P.IsPrime] {i : Nat} (hi : i < e) {a : S} (a_mem : a in P ^ i) (a_
notMem : a ∉ P ^ (i + 1)) : Function.Surjective (quotientToQuotientRangePowQuotS
ucc p P a_mem)
参数：hP0 : P != ⊥；hi : i < e；a_mem : a in P ^ i；a_notMem : a ∉ P ^ (i + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Ideal.irreducible_pow_sup`：irreducible_pow_sup (hI : I != ⊥) (hJ : Irred
ucible J) (n : Nat) : J ^ n ⊔ I = J ^ min ((normalizedFactors I).count J) n
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.prime_iff_isPrime`：prime_iff_isPrime {P : Ideal A} (hP : P != ⊥) :
 Prime P ↔ IsPrime P
· 使用定理 `Ideal.count_normalizedFactors_eq`：count_normalizedFactors_eq {p x : Idea
l R} [hp : p.IsPrime] {n : Nat} (hle : x <= p ^ n) (hlt : ¬x <= p ^ (n + 1)) : (
normalizedFactors x).c…
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Ideal.mem_quotient_iff_mem_sup`：mem_quotient_iff_mem_sup {I J : Ideal R}
 [I.IsTwoSided] {x : R} : Quotient.mk I x in J.map (Quotient.mk I) ↔ x in J ⊔ I
· 使用定理 `Ideal.Quotient.mk_eq_mk`：mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R
 ⧸ I) = mk I x
· 使用定理 `Submodule.Quotient.quot_mk_eq_mk`：quot_mk_eq_mk {p : Submodule R M} (x :
 M) : (Quot.mk _ x : M ⧸ p) = mk x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.quotientToQuotientRangePowQuotSucc_mk`：quotientToQuotientRangePowQ
uotSucc_mk {i : Nat} {a : S} (a_mem : a in P ^ i) (x : S) : quotientToQuotientRa
ngePowQuotSucc p P a_mem (Submodu…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 39 条，此处仅展示前 30 条）
-/
theorem quotientToQuotientRangePowQuotSucc_surjective [IsDedekindDomain S]
    (hP0 : P ≠ ⊥) [hP : P.IsPrime] {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i)
    (a_notMem : a ∉ P ^ (i + 1)) :
    Function.Surjective (quotientToQuotientRangePowQuotSucc p P a_mem) := by
  rintro ⟨⟨⟨x⟩, hx⟩⟩
  have Pe_le_Pi : P ^ e ≤ P ^ i := Ideal.pow_le_pow_right hi.le
  rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
    sup_eq_left.mpr Pe_le_Pi] at hx
  suffices hx' : x ∈ Ideal.span {a} ⊔ P ^ (i + 1) by
    obtain ⟨y', hy', z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, quotientToQuotientRangePowQuotSucc_mk,
      Submodule.Quotient.eq, LinearMap.mem_range, Subtype.ext_iff,
      Submodule.coe_sub]
    refine ⟨⟨_, Ideal.mem_map_of_mem _ (Submodule.neg_mem _ hz)⟩, ?_⟩
    rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Ideal.Quotient.mk_eq_mk, map_add,
      sub_add_cancel_left, map_neg]
  rw [← Submodule.span_singleton_le_iff_mem, submodule_span_eq] at a_mem a_notMem
  have hspan0 : span {a} ≠ ⊥ := fun ha ↦ a_notMem (ha ▸ bot_le)
  rwa [sup_comm, irreducible_pow_sup hspan0 ((prime_iff_isPrime hP0).mpr hP).irreducible,
    count_normalizedFactors_eq a_mem a_notMem, min_eq_left i.le_succ]

/-- Quotienting `P^i / P^e` by its subspace `P^(i+1) ⧸ P^e` is
`R ⧸ p`-linearly isomorphic to `S ⧸ P`. -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.quotientRangePowQuotSuccInclusionEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`
。
形式化陈述：quotientRangePowQuotSuccInclusionEquiv [IsDedekindDomain S] [P.IsPrime] (h
P : P != ⊥) {i : Nat} (hi : i < e) : ((P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ 
LinearMap.range (powQuotSuccInclusion p P i)) ≃ₗ[R ⧸ p] S ⧸ P
参数：hP : P != ⊥；hi : i < e。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quotienting `P^i / P^e` by its subspace `P^(i+1) ⧸ P^e` is
`R ⧸ p`-linearly isomorphic to `S ⧸ P`.
-/
noncomputable def quotientRangePowQuotSuccInclusionEquiv [IsDedekindDomain S]
    [P.IsPrime] (hP : P ≠ ⊥) {i : ℕ} (hi : i < e) :
    ((P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i))
      ≃ₗ[R ⧸ p] S ⧸ P := by
  choose a a_mem a_notMem using
    SetLike.exists_of_lt
      (Ideal.pow_right_strictAnti P hP (Ideal.IsPrime.ne_top inferInstance) (le_refl i.succ))
  refine (LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩).symm
  · exact quotientToQuotientRangePowQuotSucc p P a_mem
  · exact quotientToQuotientRangePowQuotSucc_injective p P hi a_mem a_notMem
  · exact quotientToQuotientRangePowQuotSucc_surjective p P hP hi a_mem a_notMem

/-- Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to `P / S`,
`[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]` -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.rank_pow_quot_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：rank_pow_quot_aux [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P 
!= ⊥) {i : Nat} (hi : i < e) : Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk
 (P ^ e)) (P ^ i)) = Module.rank (R ⧸ p) (S ⧸ P) + Module.rank (R ⧸ p) (Ideal.ma
p (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1)))
参数：hP0 : P != ⊥；hi : i < e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_range_of_injective`：rank_range_of_injective (f : M ->ₗ[R] M₁) (h : 
Injective f) : Module.rank R (LinearMap.range f) = Module.rank R M
· 使用定理 `Ideal.powQuotSuccInclusion_injective`：powQuotSuccInclusion_injective (i 
: Nat) : Function.Injective (powQuotSuccInclusion p P i)
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用引理 `Submodule.rank_quotient_add_rank`：Submodule.rank_quotient_add_rank (N : 
Submodule R M) : Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime

--- 原说明 ---
Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to
 `P / S`,
`[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]`
-/
theorem rank_pow_quot_aux [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    {i : ℕ} (hi : i < e) :
    Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) =
      Module.rank (R ⧸ p) (S ⧸ P) +
        Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1))) := by
  rw [← rank_range_of_injective _ (powQuotSuccInclusion_injective p P i),
    (quotientRangePowQuotSuccInclusionEquiv p P hP0 hi).symm.rank_eq]
  exact (Submodule.rank_quotient_add_rank (LinearMap.range (powQuotSuccInclusion p P i))).symm

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.rank_pow_quot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：rank_pow_quot [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P != ⊥
) (i : Nat) (hi : i <= e) : Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P
 ^ e)) (P ^ i)) = (e - i) • Module.rank (R ⧸ p) (S ⧸ P)
参数：hP0 : P != ⊥；i : Nat；hi : i <= e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.rank_pow_quot_aux`：rank_pow_quot_aux [IsDedekindDomain S] [p.IsMax
imal] [P.IsPrime] (hP0 : P != ⊥) {i : Nat} (hi : i < e) : Module.rank (R ⧸ p) (I
deal.map (Ide…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `succ_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n +
 1) • a = a + n • a
· 使用定理 `Nat.sub_succ`：∀ (n m : ℕ), n - m.succ = (n - m).pred
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Nat.sub_pos_of_lt`：∀ {m n : ℕ}, m < n → 0 < n - m
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥
· 使用定理 `rank_bot`：rank_bot : Module.rank R (⊥ : Submodule R M) = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem rank_pow_quot [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    (i : ℕ) (hi : i ≤ e) :
    Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) =
      (e - i) • Module.rank (R ⧸ p) (S ⧸ P) := by
  let Q : ℕ → Prop :=
    fun i => Module.rank (R ⧸ p) { x // x ∈ map (Quotient.mk (P ^ e)) (P ^ i) }
      = (e - i) • Module.rank (R ⧸ p) (S ⧸ P)
  refine Nat.decreasingInduction' (P := Q) (fun j lt_e _le_j ih => ?_) hi ?_
  · dsimp only [Q]
    rw [rank_pow_quot_aux p P _ lt_e, ih, ← succ_nsmul', Nat.sub_succ, ← Nat.succ_eq_add_one,
      Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt lt_e)]
    assumption
  · dsimp only [Q]
    rw [Nat.sub_self, zero_nsmul, map_quotient_self]
    exact rank_bot (R ⧸ p) (S ⧸ P ^ e)

end

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.rank_prime_pow_ramificationIdx** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：rank_prime_pow_ramificationIdx [IsDedekindDomain S] [p.IsMaximal] [P.IsPri
me] (hP0 : P != ⊥) (he : e != 0) : Module.rank (R ⧸ p) (S ⧸ P ^ e) = e • @Module
.rank (R ⧸ p) (S ⧸ P) _ _ (@Algebra.toModule _ _ _ _ <| @Quotient.algebraQuotien
tOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩)
参数：hP0 : P != ⊥；he : e != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.rank_pow_quot`：rank_pow_quot [IsDedekindDomain S] [p.IsMaximal] [P
.IsPrime] (hP0 : P != ⊥) (i : Nat) (hi : i <= e) : Module.rank (R ⧸ p) (Ideal.ma
p (Ideal.…
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_top`：rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Nat.sub_zero`：∀ (n : ℕ), n - 0 = n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1

--- 原说明 ---
If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`.
-/
theorem rank_prime_pow_ramificationIdx [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime]
    (hP0 : P ≠ ⊥) (he : e ≠ 0) :
    Module.rank (R ⧸ p) (S ⧸ P ^ e) =
      e •
        @Module.rank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <|
            @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩) := by
  let : NeZero e := ⟨he⟩
  have := rank_pow_quot p P hP0 0 (Nat.zero_le e)
  rw [pow_zero, Nat.sub_zero, Ideal.one_eq_top, Ideal.map_top] at this
  exact (rank_top (R ⧸ p) _).symm.trans this

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]`, as a natural number, is equal to `e * [S/P : R/p]`. -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.finrank_prime_pow_ramificationIdx** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：finrank_prime_pow_ramificationIdx [IsDedekindDomain S] (hP0 : P != ⊥) [p.I
sMaximal] [P.IsPrime] (he : e != 0) : finrank (R ⧸ p) (S ⧸ P ^ e) = e * @finrank
 (R ⧸ p) (S ⧸ P) _ _ (@Algebra.toModule _ _ _ _ <| @Quotient.algebraQuotientOfRa
mificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩)
参数：hP0 : P != ⊥；he : e != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.rank_prime_pow_ramificationIdx`：rank_prime_pow_ramificationIdx [Is
DedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P != ⊥) (he : e != 0) : Modul
e.rank (R ⧸ p) (S ⧸ P ^ e)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.finiteDimensional_iff_of_rank_eq_nsmul`：finiteDimensional_iff_of_
rank_eq_nsmul {W} [AddCommGroup W] [Module K W] {n : Nat} (hn : n != 0) (hVW : M
odule.rank K V = n • Module.rank K …
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_rank'`：finrank_eq_rank' [FiniteDimensional K V] : (fin
rank K V : Cardinal.{v}) = Module.rank K V
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.finrank_of_infinite_dimensional`：finrank_of_infinite_dimensional 
(h : ¬FiniteDimensional K V) : finrank K V = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]`, as a natural number, is equal to `e * [S/P
 : R/p]`.
-/
theorem finrank_prime_pow_ramificationIdx [IsDedekindDomain S] (hP0 : P ≠ ⊥)
    [p.IsMaximal] [P.IsPrime] (he : e ≠ 0) :
    finrank (R ⧸ p) (S ⧸ P ^ e) =
      e *
        @finrank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <|
            @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩) := by
  let : NeZero e := ⟨he⟩
  let : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfRamificationIdxNeZero p P
  have hdim := rank_prime_pow_ramificationIdx _ _ hP0 he
  by_cases hP : FiniteDimensional (R ⧸ p) (S ⧸ P)
  · have := (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mpr hP
    apply @Nat.cast_injective Cardinal
    rw [finrank_eq_rank', Nat.cast_mul, finrank_eq_rank', hdim, nsmul_eq_mul]
  have hPe := mt (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mp hP
  simp only [finrank_of_infinite_dimensional hP, finrank_of_infinite_dimensional hPe,
    mul_zero]

end FactLeComap

section FactorsMap

/-! ## Properties of the factors of `p.map (algebraMap R S)` -/


variable [IsDedekindDomain S]

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Factors`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekindDomain S] (P : ↥(UniqueFa
ctorizationMonoid.factors (Ideal.map (algebraMap R S) p)).toFinset),   ↑P ≠ ⊥
参数：p : Ideal R；P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R 
S) p)).toFinset。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `UniqueFactorizationMonoid.prime_of_factor`：prime_of_factor {a : α} (x : 
α) (hx : x in factors a) : Prime x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Factors.ne_bot (P : (factors (map (algebraMap R S) p)).toFinset) : (P : Ideal S) ≠ ⊥ :=
  (prime_of_factor _ (Multiset.mem_toFinset.mp P.2)).ne_zero

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Factors`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekindDomain S] (P : ↥(UniqueFa
ctorizationMonoid.factors (Ideal.map (algebraMap R S) p)).toFinset),   (↑P).IsPr
ime
参数：p : Ideal R；P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R 
S) p)).toFinset；↑P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `UniqueFactorizationMonoid.prime_of_factor`：prime_of_factor {a : α} (x : 
α) (hx : x in factors a) : Prime x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance Factors.isPrime (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsPrime (P : Ideal S) :=
  Ideal.isPrime_of_prime (prime_of_factor _ (Multiset.mem_toFinset.mp P.2))

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.ramificationIdx_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Factors
`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekindDomain S] (P : ↥(UniqueFa
ctorizationMonoid.factors (Ideal.map (algebraMap R S) p)).toFinset),   p.ramific
ationIdx' ↑P ≠ 0
参数：p : Ideal R；P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R 
S) p)).toFinset。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero`：∀ {R : Type u} [inst : 
CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {p : Ideal
 R} {P : Ideal S}   [IsDedekindDomain…
· 使用定理 `UniqueFactorizationMonoid.ne_zero_of_mem_factors`：ne_zero_of_mem_factors
 {p a : α} (h : p in factors a) : a != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Ideal.Factors.isPrime`：∀ {R : Type u} [inst : CommRing R] {S : Type v} [
inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekind
Domain S] (…
· 使用定理 `Ideal.le_of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {I J : Ideal R},
 I ∣ J → J ≤ I
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_factors`：dvd_of_mem_factors {p a : 
α} (h : p in factors a) : p ∣ a
-/
theorem Factors.ramificationIdx_ne_zero (P : (factors (map (algebraMap R S) p)).toFinset) :
    ramificationIdx' p P.1 ≠ 0 :=
  IsDedekindDomain.ramificationIdx'_ne_zero (ne_zero_of_mem_factors (Multiset.mem_toFinset.mp P.2))
    (Factors.isPrime p P) (Ideal.le_of_dvd (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2)))

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.fact_ramificationIdx_neZero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Fac
tors`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekindDomain S] (P : ↥(UniqueFa
ctorizationMonoid.factors (Ideal.map (algebraMap R S) p)).toFinset),   NeZero (p
.ramificationIdx' ↑P)
参数：p : Ideal R；P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R 
S) p)).toFinset；p.ramificationIdx' ↑P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Factors.ramificationIdx_ne_zero`：∀ {R : Type u} [inst : CommRing R
] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [ins
t_3 : IsDedekindDomain S] (…
-/
instance Factors.fact_ramificationIdx_neZero (P : (factors (map (algebraMap R S) p)).toFinset) :
    NeZero (ramificationIdx' p P.1) :=
  ⟨Factors.ramificationIdx_ne_zero p P⟩

attribute [local instance] Quotient.algebraQuotientOfRamificationIdxNeZero

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Factors`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekindDomain S] (P : ↥(UniqueFa
ctorizationMonoid.factors (Ideal.map (algebraMap R S) p)).toFinset),   IsScalarT
ower R (R ⧸ p) (S ⧸ ↑P)
参数：p : Ideal R；P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R 
S) p)).toFinset；R ⧸ p；S ⧸ ↑P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Ideal.Factors.fact_ramificationIdx_neZero`：∀ {R : Type u} [inst : CommRi
ng R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   
[inst_3 : IsDedekindDomain S] (…
-/
instance Factors.isScalarTower (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsScalarTower R (R ⧸ p) (S ⧸ (P : Ideal S)) :=
  IsScalarTower.of_algebraMap_eq' rfl

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.liesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Factors`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekindDomain S] [p.IsMaximal]  
 (P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R S) p)).toFins
et), (↑P).LiesOver p
参数：p : Ideal R；P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R 
S) p)).toFinset；↑P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_eq_of_scalar_tower_quotient`：comap_eq_of_scalar_tower_quotie
nt [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)] [IsScalarTower R (R ⧸ p) (S ⧸ P)] (h 
: Function.Injective (algebra…
· 使用定理 `Ideal.Factors.fact_ramificationIdx_neZero`：∀ {R : Type u} [inst : CommRi
ng R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   
[inst_3 : IsDedekindDomain S] (…
· 使用定理 `Ideal.Factors.isScalarTower`：∀ {R : Type u} [inst : CommRing R] {S : Typ
e v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDe
dekindDomain S] (…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Factors.isPrime`：∀ {R : Type u} [inst : CommRing R] {S : Type v} [
inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekind
Domain S] (…
-/
instance Factors.liesOver [p.IsMaximal] (P : (factors (map (algebraMap R S) p)).toFinset) :
    P.1.LiesOver p :=
  ⟨(comap_eq_of_scalar_tower_quotient (algebraMap (R ⧸ p) (S ⧸ P.1)).injective).symm⟩

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.finrank_pow_ramificationIdx** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Fac
tors`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekindDomain S] [p.IsMaximal]  
 (P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R S) p)).toFins
et),   Module.finrank (R ⧸ p) (S ⧸ ↑P ^ p.ramificationIdx' ↑P) = p.ramificationI
dx' ↑P * p.inertiaDeg' ↑P
参数：p : Ideal R；P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R 
S) p)).toFinset；R ⧸ p；S ⧸ ↑P ^ p.ramificationIdx' ↑P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Ideal.Factors.fact_ramificationIdx_neZero`：∀ {R : Type u} [inst : CommRi
ng R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   
[inst_3 : IsDedekindDomain S] (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.finrank_prime_pow_ramificationIdx`：finrank_prime_pow_ramificationI
dx [IsDedekindDomain S] (hP0 : P != ⊥) [p.IsMaximal] [P.IsPrime] (he : e != 0) :
 finrank (R ⧸ p) (S ⧸ P ^ e) …
· 使用定理 `Ideal.Factors.ne_bot`：∀ {R : Type u} [inst : CommRing R] {S : Type v} [i
nst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekindD
omain S] (…
· 使用定理 `Ideal.Factors.isPrime`：∀ {R : Type u} [inst : CommRing R] {S : Type v} [
inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekind
Domain S] (…
· 使用定理 `Ideal.Factors.liesOver`：∀ {R : Type u} [inst : CommRing R] {S : Type v} 
[inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekin
dDomain S] […
· 使用定理 `Ideal.inertiaDeg'_algebraMap`：∀ {R : Type u} [inst : CommRing R] {S : Ty
pe v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)  
 [inst_3 : P.LiesO…
-/
theorem Factors.finrank_pow_ramificationIdx [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx' p P.1) =
      ramificationIdx' p P.1 * inertiaDeg' p (P : Ideal S) := by
  rw [finrank_prime_pow_ramificationIdx, inertiaDeg'_algebraMap]
  exacts [Factors.ne_bot p P, NeZero.ne _]

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.finiteDimensional_quotient_pow** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.
Factors`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekindDomain S] [Module.Finite 
R S] [inst_5 : p.IsMaximal]   (P : ↥(UniqueFactorizationMonoid.factors (Ideal.ma
p (algebraMap R S) p)).toFinset),   FiniteDimensional (R ⧸ p) (S ⧸ ↑P ^ p.ramifi
cationIdx' ↑P)
参数：p : Ideal R；P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R 
S) p)).toFinset；R ⧸ p；S ⧸ ↑P ^ p.ramificationIdx' ↑P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_finrank_pos`：of_finrank_pos (h : 0 < finrank K V) :
 FiniteDimensional K V
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Ideal.Factors.finrank_pow_ramificationIdx`：∀ {R : Type u} [inst : CommRi
ng R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   
[inst_3 : IsDedekindDomain S] […
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Ideal.Factors.ramificationIdx_ne_zero`：∀ {R : Type u} [inst : CommRing R
] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [ins
t_3 : IsDedekindDomain S] (…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ideal.inertiaDeg'_pos`：∀ {R : Type u} [inst : CommRing R] {S : Type v} [
inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   [p.IsM
aximal] [Mo…
· 使用定理 `Ideal.Factors.liesOver`：∀ {R : Type u} [inst : CommRing R] {S : Type v} 
[inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   [inst_3 : IsDedekin
dDomain S] […
-/
instance Factors.finiteDimensional_quotient_pow [Module.Finite R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    FiniteDimensional (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx' p P.1) := by
  refine .of_finrank_pos ?_
  rw [pos_iff_ne_zero, Factors.finrank_pow_ramificationIdx]
  exact mul_ne_zero (Factors.ramificationIdx_ne_zero p P) (inertiaDeg'_pos p P.1).ne'

universe w

/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : Ideal R`
factors in `S` as `∏ i, P i ^ e i`, then `S ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.piQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Factors`。
形式化陈述：{R : Type u} →   [inst : CommRing R] →     {S : Type v} →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           [inst_3 : IsDedekindDom
ain S] →             (p : Ideal R) →               Ideal.map (algebraMap R S) p 
≠ ⊥ →                 S ⧸ Ideal.map (algebraMap R S) p ≃+*                   ((P
 : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R S) p)).toFinset)
 →                     S ⧸ ↑P ^ p.ramificationIdx' ↑P)
参数：p : Ideal R；algebraMap R S；algebraMap R S；(P : ↥(UniqueFactorizationMonoid.fa
ctors (Ideal.map (algebraMap R S) p)).toFinset) →                     S ⧸ ↑P ^ p
.ramificationIdx' ↑P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Chinese remainder theorem** for a ring of integers: if the prime ideal `p : Id
eal R`
factors in `S` as `∏ i, P i ^ e i`, then `S ⧸ I` factors as `Π i, R ⧸ (P i ^ e i
)`.
-/
noncomputable def Factors.piQuotientEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    S ⧸ map (algebraMap R S) p ≃+*
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx' p P.1 :=
  (IsDedekindDomain.quotientEquivPiFactors hp).trans <|
    @RingEquiv.piCongrRight (factors (map (algebraMap R S) p)).toFinset
      (fun P => S ⧸ (P : Ideal S) ^ (factors (map (algebraMap R S) p)).count (P : Ideal S))
      (fun P => S ⧸ (P : Ideal S) ^ ramificationIdx' p P.1) _ _
      fun P : (factors (map (algebraMap R S) p)).toFinset =>
      Ideal.quotEquivOfEq <| by
        rw [IsDedekindDomain.ramificationIdx'_eq_factors_count hp (Factors.isPrime p P)
            (Factors.ne_bot p P)]

@[simp, deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.piQuotientEquiv_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Factors`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   [inst_3 : IsDedekindDomain S] (p : Ideal R) (hp : Ideal.map
 (algebraMap R S) p ≠ ⊥) (x : S),   (Ideal.Factors.piQuotientEquiv p hp) ((Ideal
.Quotient.mk (Ideal.map (algebraMap R S) p)) x) = fun x_1 =>     (Ideal.Quotient
.mk (↑x_1 ^ p.ramificationIdx' ↑x_1)) x
参数：p : Ideal R；hp : Ideal.map (algebraMap R S) p ≠ ⊥；x : S；Ideal.Factors.piQuoti
entEquiv p hp；(Ideal.Quotient.mk (Ideal.map (algebraMap R S) p)) x；Ideal.Quotien
t.mk (↑x_1 ^ p.ramificationIdx' ↑x_1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem Factors.piQuotientEquiv_mk (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    Factors.piQuotientEquiv p hp (Ideal.Quotient.mk _ x) = fun _ => Ideal.Quotient.mk _ x := rfl

@[simp, deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.piQuotientEquiv_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Factors`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   [inst_3 : IsDedekindDomain S] (p : Ideal R) (hp : Ideal.map
 (algebraMap R S) p ≠ ⊥) (x : R),   (Ideal.Factors.piQuotientEquiv p hp) ((algeb
raMap R (S ⧸ Ideal.map (algebraMap R S) p)) x) = fun x_1 =>     (Ideal.Quotient.
mk (↑x_1 ^ p.ramificationIdx' ↑x_1)) ((algebraMap R S) x)
参数：p : Ideal R；hp : Ideal.map (algebraMap R S) p ≠ ⊥；x : R；Ideal.Factors.piQuoti
entEquiv p hp；(algebraMap R (S ⧸ Ideal.map (algebraMap R S) p)) x；Ideal.Quotient
.mk (↑x_1 ^ p.ramificationIdx' ↑x_1)；(algebraMap R S) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem Factors.piQuotientEquiv_map (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : R) :
    Factors.piQuotientEquiv p hp (algebraMap _ _ x) = fun _ =>
      Ideal.Quotient.mk _ (algebraMap _ _ x) := rfl

variable (S)

/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : Ideal R`
factors in `S` as `∏ i, P i ^ e i`,
then `S ⧸ I` factors `R ⧸ I`-linearly as `Π i, R ⧸ (P i ^ e i)`. -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.Factors.piQuotientLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Factors`。
形式化陈述：{R : Type u} →   [inst : CommRing R] →     (S : Type v) →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           [inst_3 : IsDedekindDom
ain S] →             (p : Ideal R) →               Ideal.map (algebraMap R S) p 
≠ ⊥ →                 (S ⧸ Ideal.map (algebraMap R S) p) ≃ₗ[R ⧸ p]              
     (P : ↥(UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R S) p)).to
Finset) →                     S ⧸ ↑P ^ p.ramificationIdx' ↑P
参数：S : Type v；p : Ideal R；algebraMap R S；S ⧸ Ideal.map (algebraMap R S) p；P : ↥(
UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R S) p)).toFinset。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Chinese remainder theorem** for a ring of integers: if the prime ideal `p : Id
eal R`
factors in `S` as `∏ i, P i ^ e i`,
then `S ⧸ I` factors `R ⧸ I`-linearly as `Π i, R ⧸ (P i ^ e i)`.
-/
noncomputable def Factors.piQuotientLinearEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    (S ⧸ map (algebraMap R S) p) ≃ₗ[R ⧸ p]
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx' p P.1 :=
  { Factors.piQuotientEquiv p hp with
    map_smul' := by
      rintro ⟨c⟩ ⟨x⟩; ext P
      simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, Algebra.smul_def,
        Quotient.algebraMap_quotient_map_quotient, Quotient.mk_algebraMap,
        RingHomCompTriple.comp_apply, Pi.mul_apply, Pi.algebraMap_apply]
      congr }

variable (K L : Type*) [Field K] [Field L] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [Module.Finite R S]

/-- The **fundamental identity** of ramification index `e` and inertia degree `f`:
for `P` ranging over the primes lying over `p`, `∑ P, e P * f P = [Frac(S) : Frac(R)]`;
here `S` is a finite `R`-module (and thus `Frac(S) : Frac(R)` is a finite extension) and `p`
is maximal. -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.sum_ramification_inertia** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：sum_ramification_inertia {p : Ideal R} [p.IsMaximal] (hp0 : p != ⊥) : ∑ P 
in IsDedekindDomain.primesOverFinset p S, ramificationIdx' p P * inertiaDeg' p P
 = finrank K L
参数：hp0 : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Ideal.Factors.finrank_pow_ramificationIdx`：∀ {R : Type u} [inst : CommRi
ng R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   
[inst_3 : IsDedekindDomain S] […
· 使用定理 `Module.finrank_pi_fintype`：Module.finrank_pi_fintype {ι : Type v} [Finty
pe ι] {M : ι -> Type w} [forall i : ι, AddCommMonoid (M i)] [forall i : ι, Modul
e R (M i)] [for…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.Factors.finiteDimensional_quotient_pow`：∀ {R : Type u} [inst : Com
mRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)
   [inst_3 : IsDedekindDomain S] […
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.map_eq_bot_iff_le_ker`：map_eq_bot_iff_le_ker {I : Ideal R} (f : F)
 : I.map f = ⊥ ↔ I <= RingHom.ker f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `algebraMap_injective_of_field_isFractionRing`：algebraMap_injective_of_fi
eld_isFractionRing (K L : Type*) [Field K] [Semiring L] [Nontrivial L] [Algebra 
R K] [IsFractionRing R K] [Algebra…
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Ideal.finrank_quotient_map`：finrank_quotient_map [IsDomain S] [IsDedekin
dDomain R] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S 
L] [hp : p.IsMax…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A

--- 原说明 ---
The **fundamental identity** of ramification index `e` and inertia degree `f`:
for `P` ranging over the primes lying over `p`, `∑ P, e P * f P = [Frac(S) : Fra
c(R)]`;
here `S` is a finite `R`-module (and thus `Frac(S) : Frac(R)` is a finite extens
ion) and `p`
is maximal.
-/
theorem sum_ramification_inertia {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p S,
        ramificationIdx' p P * inertiaDeg' p P = finrank K L := by
  set e := ramificationIdx' p (S := S)
  calc
    ∑ P ∈ (factors (map (algebraMap R S) p)).toFinset, e P * inertiaDeg' p P =
        ∑ P ∈ (factors (map (algebraMap R S) p)).toFinset.attach,
          finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ e P) := ?_
    _ = finrank (R ⧸ p)
          (∀ P : (factors (map (algebraMap R S) p)).toFinset, S ⧸ (P : Ideal S) ^ e P) :=
      (finrank_pi_fintype (R ⧸ p)).symm
    _ = finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) := ?_
    _ = finrank K L := ?_
  · rw [← Finset.sum_attach]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Factors.finrank_pow_ramificationIdx]
  · refine LinearEquiv.finrank_eq (Factors.piQuotientLinearEquiv S p ?_).symm
    rwa [Ne, Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp <|
      algebraMap_injective_of_field_isFractionRing R S K L, le_bot_iff]
  · exact finrank_quotient_map p K L

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.inertiaDeg_le_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg_le_finrank [NoZeroSMulDivisors R S] {p : Ideal R} [p.IsMaximal]
 (P : Ideal S) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver p] (hp0 : p != ⊥) : p.inertia
Deg' P <= Module.finrank K L
参数：P : Ideal S；hp0 : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsDedekindDomain.mem_primesOverFinset_iff`：mem_primesOverFinset_iff {P :
 Ideal B} : P in primesOverFinset p B ↔ P in primesOver p B
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.sum_ramification_inertia`：sum_ramification_inertia {p : Ideal R} [
p.IsMaximal] (hp0 : p != ⊥) : ∑ P in IsDedekindDomain.primesOverFinset p S, rami
ficationIdx' p P * i…
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_mul_of_pos_left`：∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver`：∀ {R : Type
 u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S
] [IsDedekindDomain S]   [IsDomain R] [Module.IsT…
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem inertiaDeg_le_finrank [NoZeroSMulDivisors R S] {p : Ideal R} [p.IsMaximal]
    (P : Ideal S) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver p] (hp0 : p ≠ ⊥) :
    p.inertiaDeg' P ≤ Module.finrank K L := by
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hP₁, hP₂⟩
  rw [← sum_ramification_inertia S K L hp0, ← Finset.add_sum_erase _ _ hP]
  refine le_trans (Nat.le_mul_of_pos_left _ ?_) (Nat.le_add_right _ _)
  exact Nat.pos_iff_ne_zero.mpr <| IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ hp0

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.ramificationIdx_le_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ramificationIdx_le_finrank [NoZeroSMulDivisors R S] {p : Ideal R} [p.IsMax
imal] (P : Ideal S) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver p] : p.ramificationIdx' 
P <= Module.finrank K L
参数：P : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ramificationIdx'_bot`：∀ {R : Type u} [inst : CommRing R] {S : Type
 v} [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Ideal S},   ⊥.ramification
Idx' P = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsDedekindDomain.mem_primesOverFinset_iff`：mem_primesOverFinset_iff {P :
 Ideal B} : P in primesOverFinset p B ↔ P in primesOver p B
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.sum_ramification_inertia`：sum_ramification_inertia {p : Ideal R} [
p.IsMaximal] (hp0 : p != ⊥) : ∑ P in IsDedekindDomain.primesOverFinset p S, rami
ficationIdx' p P * i…
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Ideal.inertiaDeg'_ne_zero`：∀ {R : Type u} [inst : CommRing R] {S : Type 
v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   [p
.IsMaximal] [Mo…
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem ramificationIdx_le_finrank [NoZeroSMulDivisors R S] {p : Ideal R} [p.IsMaximal]
    (P : Ideal S) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver p] :
    p.ramificationIdx' P ≤ Module.finrank K L := by
  by_cases hp0 : p = ⊥
  · simp [hp0]
  have hP : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mpr ⟨hP₁, hP₂⟩
  rw [← sum_ramification_inertia S K L hp0, ← Finset.add_sum_erase _ _ hP]
  refine le_trans (Nat.le_mul_of_pos_right _ ?_) (Nat.le_add_right _ _)
  exact Nat.pos_iff_ne_zero.mpr <| inertiaDeg'_ne_zero p P

@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.card_primesOverFinset_le_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：card_primesOverFinset_le_finrank [NoZeroSMulDivisors R S] {p : Ideal R} [p
.IsMaximal] (hp0 : p != ⊥) : Finset.card (IsDedekindDomain.primesOverFinset p S)
 <= Module.finrank K L
参数：hp0 : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.sum_ramification_inertia`：sum_ramification_inertia {p : Ideal R} [
p.IsMaximal] (hp0 : p != ⊥) : ∑ P in IsDedekindDomain.primesOverFinset p S, rami
ficationIdx' p P * i…
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsDedekindDomain.mem_primesOverFinset_iff`：mem_primesOverFinset_iff {P :
 Ideal B} : P in primesOverFinset p B ↔ P in primesOver p B
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Right.one_le_mul`：Right.one_le_mul [MulRightMono α] {a b : α} (ha : 1 <=
 a) (hb : 1 <= b) : 1 <= a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver`：∀ {R : Type
 u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [inst_2 : Algebra R S
] [IsDedekindDomain S]   [IsDomain R] [Module.IsT…
· 使用定理 `Ideal.inertiaDeg'_ne_zero`：∀ {R : Type u} [inst : CommRing R] {S : Type 
v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   [p
.IsMaximal] [Mo…
-/
theorem card_primesOverFinset_le_finrank [NoZeroSMulDivisors R S] {p : Ideal R} [p.IsMaximal]
    (hp0 : p ≠ ⊥) : Finset.card (IsDedekindDomain.primesOverFinset p S) ≤ Module.finrank K L := by
  rw [← sum_ramification_inertia S K L hp0, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun P hP ↦ ?_
  have : P.IsPrime := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP).1
  have : P.LiesOver p := ((IsDedekindDomain.mem_primesOverFinset_iff hp0 _).mp hP).2
  refine Right.one_le_mul ?_ ?_
  · exact Nat.pos_iff_ne_zero.mpr <| IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ hp0
  · exact Nat.pos_iff_ne_zero.mpr <| inertiaDeg'_ne_zero p P

/-- `Ideal.sum_ramification_inertia`, in the local (DVR) case. -/
@[deprecated "Use results of RingTheory.RamificationInertia.Basic" (since := "2026-07-01")]
/-
**Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing** 是 Mathlib 中的一个引理，位于命名空间 
`Ideal`。
形式化陈述：ramificationIdx_mul_inertiaDeg_of_isLocalRing [IsLocalRing S] {p : Ideal R
} [p.IsMaximal] (hp0 : p != ⊥) : ramificationIdx' p (IsLocalRing.maximalIdeal S)
 * p.inertiaDeg' (IsLocalRing.maximalIdeal S) = Module.finrank K L
参数：hp0 : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.of_field_isFractionRing`：FaithfulSMul.of_field_isFractionRi
ng (K L : Type*) [Field K] [Semiring L] [Nontrivial L] [Algebra R K] [IsFraction
Ring R K] [Algebra S L] [A…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.sum_ramification_inertia`：sum_ramification_inertia {p : Ideal R} [
p.IsMaximal] (hp0 : p != ⊥) : ∑ P in IsDedekindDomain.primesOverFinset p S, rami
ficationIdx' p P * i…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsLocalRing.primesOverFinset_eq`：IsLocalRing.primesOverFinset_eq [IsLoca
lRing A] [IsDedekindDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R 
A] {p : Ideal R} [p.I…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`Ideal.sum_ramification_inertia`, in the local (DVR) case.
-/
lemma ramificationIdx_mul_inertiaDeg_of_isLocalRing [IsLocalRing S] {p : Ideal R} [p.IsMaximal]
    (hp0 : p ≠ ⊥) :
    ramificationIdx' p (IsLocalRing.maximalIdeal S) *
      p.inertiaDeg' (IsLocalRing.maximalIdeal S) = Module.finrank K L := by
  have := FaithfulSMul.of_field_isFractionRing R S K L
  simp_rw [← sum_ramification_inertia S K L hp0, IsLocalRing.primesOverFinset_eq S hp0,
    Finset.sum_singleton]

end FactorsMap

end Ideal

