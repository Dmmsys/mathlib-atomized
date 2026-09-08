/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Unramified algebras over local rings

## Main results
- `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`:
  Let `R` be a local ring, `A` be a local `R`-algebra essentially of finite type.
  Then `A/R` is unramified if and only if `κA/κR` is separable, and `m_R S = m_S`.
- `Algebra.isUnramifiedAt_iff_map_eq`:
  Let `A` be an essentially of finite type `R`-algebra, `q` be a prime over `p`.
  Then `A` is unramified at `p` if and only if `κ(q)/κ(p)` is separable, and `pS_q = qS_q`.

Let `S` be an `R` algebra, `p` be a prime of `R`, and suppose `q` is the unique prime of `S`
lying over `R`, then
- `Localization.localRingHom_injective_of_primesOver_eq_singleton`:
  If `R ⊆ S` is integral, then `R_p → S_q` is injective.
- `Localization.localRingHom_surjective_of_primesOver_eq_singleton`:
  Suppose `S` is `R`-finite and unramified at `q`. If `κ(p) = κ(q)` then `R_p → S_q` is surjective.
- `Localization.exists_awayMap_bijective_of_residueField_surjective`:
  Suppose `R ⊆ S` is finite and unramified at `q`.
  If `κ(p) = κ(q)` then there exists `r ∉ p` such that `R[1/f] = S[1/f]`.
-/

@[expose] public section

open IsLocalRing

namespace Algebra

section IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FormallyUnramified S (ResidueField S) := .quotient _
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FormallyUnramified R S] :
    FormallyUnramified (ResidueField R) (ResidueField S) :=
  have : FormallyUnramified R (ResidueField S) := .comp _ S _
  .of_restrictScalars R _ _

variable [EssFiniteType R S]

@[stacks 00UW "(2)"]
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FormallyUnramified R S] :
    Module.Finite (ResidueField R) (ResidueField S) :=
  have : EssFiniteType R (ResidueField S) := .comp _ S _
  have : EssFiniteType (ResidueField R) (ResidueField S) := .of_comp R _ _
  FormallyUnramified.finite_of_free _ _

@[stacks 00UW "(2)"]
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FormallyUnramified R S] :
    Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
  FormallyUnramified.isSeparable _ _

set_option backward.inferInstanceAs.wrap.data false in
/-
**Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal** 是 Mathlib 中的一个定
理，位于命名空间 `Algebra.FormallyUnramified`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [inst_3 : IsLocalRing R] [IsLocalRing S] [IsLocalHom (a
lgebraMap R S)] [Algebra.EssFiniteType R S]   [Algebra.FormallyUnramified R S], 
IsField (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
参数：algebraMap R S；S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocalRing.local_hom_TFAE`：local_hom_TFAE (f : R ->+* S) : List.TFAE [I
sLocalHom f, f '' maximalIdeal R subseteq maximalIdeal S, (maximalIdeal R).map f
 <= maximalIdeal…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.FormallyUnramified.of_restrictScalars`：of_restrictScalars [Forma
llyUnramified R B] : FormallyUnramified A B
· 使用定理 `Algebra.EssFiniteType.of_comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type
 u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 
: Algebra R S] [ins…
· 使用定理 `Algebra.instEssFiniteTypeQuotientIdeal`：∀ (R : Type u_1) (S : Type u_2) 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssF
initeType R S] (I : Ideal S)…
· 使用引理 `Algebra.FormallyUnramified.finite_of_free`：finite_of_free [Module.Free R
 S] : Module.Finite R S
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Algebra.FormallyUnramified.isReduced_of_field`：isReduced_of_field : IsRe
duced A
· 使用定理 `isArtinian_of_tower`：isArtinian_of_tower (R) {S M} [Semiring R] [Semirin
g S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R S M
] (h : Is…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.nontrivial_iff`：∀ {R : Type u_3} [inst : Ring R] {I : Ide
al R}, Nontrivial (R ⧸ I) ↔ I ≠ ⊤
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `IsLocalRing.of_surjective'`：of_surjective' [Ring S] [Nontrivial S] (f : 
R ->+* S) (hf : Function.Surjective f) : IsLocalRing S
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.jacobson_eq_maximalIdeal`：jacobson_eq_maximalIdeal (I : Idea
l R) (h : I != ⊤) : I.jacobson = IsLocalRing.maximalIdeal R
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用引理 `IsArtinianRing.jacobson_eq_radical`：jacobson_eq_radical (I : Ideal R) : 
I.jacobson = I.radical
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `nilradical.eq_1`：∀ (R : Type u_3) [inst : CommSemiring R], nilradical R 
= Ideal.radical 0
· 使用定理 `nilradical_eq_zero`：nilradical_eq_zero (R : Type*) [CommSemiring R] [IsR
educed R] : nilradical R = 0
· 使用定理 `IsLocalRing.isField_iff_maximalIdeal_eq`：isField_iff_maximalIdeal_eq : I
sField R ↔ maximalIdeal R = ⊥
-/
lemma FormallyUnramified.isField_quotient_map_maximalIdeal [FormallyUnramified R S] :
    IsField (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  let mR := (maximalIdeal R).map (algebraMap R S)
  have hmR : mR ≤ maximalIdeal S := ((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp ‹_›
  let : Algebra (ResidueField R) (S ⧸ mR) := (inferInstanceAs <| Algebra (R ⧸ _) _)
  have : IsScalarTower R (ResidueField R) (S ⧸ mR) := (inferInstanceAs <| IsScalarTower R (R ⧸ _) _)
  have : FormallyUnramified (ResidueField R) (S ⧸ mR) := .of_restrictScalars R _ _
  have : EssFiniteType (ResidueField R) (S ⧸ mR) := .of_comp R _ _
  have : Module.Finite (ResidueField R) (S ⧸ mR) := FormallyUnramified.finite_of_free _ _
  have : IsReduced (S ⧸ mR) := FormallyUnramified.isReduced_of_field (ResidueField R) (S ⧸ mR)
  have : IsArtinianRing (S ⧸ mR) := isArtinian_of_tower (ResidueField R) inferInstance
  have : Nontrivial (S ⧸ mR) :=
    Ideal.Quotient.nontrivial_iff.mpr <| ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hmR
  have : IsLocalRing (S ⧸ mR) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : maximalIdeal (S ⧸ mR) = ⊥ := by
    rw [← jacobson_eq_maximalIdeal _ bot_ne_top, IsArtinianRing.jacobson_eq_radical,
      ← Ideal.zero_eq_bot, ← nilradical, nilradical_eq_zero]
  rwa [← isField_iff_maximalIdeal_eq] at this

@[stacks 00UW "(1)"]
/-
**Algebra.FormallyUnramified.map_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.FormallyUnramified`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [inst_3 : IsLocalRing R] [inst_4 : IsLocalRing S] [IsLo
calHom (algebraMap R S)] [Algebra.EssFiniteType R S]   [Algebra.FormallyUnramifi
ed R S], Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.m
aximalIdeal S
参数：algebraMap R S；algebraMap R S；IsLocalRing.maximalIdeal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.maximal_ideal_iff_isField_quotient`：maximal_ideal_iff_isF
ield_quotient {R} [CommRing R] (I : Ideal R) : I.IsMaximal ↔ IsField (R ⧸ I)
· 使用定理 `Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal`：∀ {R : Typ
e u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebr
a R S]   [inst_3 : IsLocalRing R] [IsLocalRing S] …
-/
lemma FormallyUnramified.map_maximalIdeal [FormallyUnramified R S] :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
  apply eq_maximalIdeal
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact isField_quotient_map_maximalIdeal

@[stacks 02FM]
/-
**Algebra.FormallyUnramified.of_map_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Alge
bra.FormallyUnramified`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [inst_3 : IsLocalRing R] [inst_4 : IsLocalRing S] [inst
_5 : IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]   [Algebra.IsSepar
able (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)],   Ideal.map (al
gebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S → Algebr
a.FormallyUnramified R S
参数：algebraMap R S；IsLocalRing.ResidueField R；IsLocalRing.ResidueField S；algebraM
ap R S；IsLocalRing.maximalIdeal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_isSeparable`：of_isSeparable [Algebra.IsSep
arable K L] : FormallyUnramified K L
· 使用定理 `Algebra.FormallyUnramified.comp`：comp [FormallyUnramified R A] [Formally
Unramified A B] : FormallyUnramified R B
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst_3
 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `Algebra.instFormallyUnramifiedResidueField`：∀ {S : Type u_2} [inst : Com
mRing S] [inst_1 : IsLocalRing S], Algebra.FormallyUnramified S (IsLocalRing.Res
idueField S)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.subsingleton_tensorProduct`：subsingleton_tensorProduct [Modu
le.Finite R M] : Subsingleton (k otimes[R] M) ↔ Subsingleton M
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`：KaehlerDif
ferential.exact_kerCotangentToTensor_mapBaseChange (h : Function.Surjective (alg
ebraMap A B)) : Function.Exact (kerCotangentToTens…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`：∀ {R : Type
 v} {A : Type u} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A
}   [self : Algebra.FormallyUnramified R A], Subs…
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Derivation.map_algebraMap`：map_algebraMap : D (algebraMap R A r) = 0
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
（共 39 条，此处仅展示前 30 条）
-/
lemma FormallyUnramified.of_map_maximalIdeal
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    (H : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Algebra.FormallyUnramified R S := by
  constructor
  have : FormallyUnramified (ResidueField R) (ResidueField S) := .of_isSeparable _ _
  have : FormallyUnramified R (ResidueField S) := .comp _ (ResidueField R) _
  rw [← subsingleton_tensorProduct (R := S)]
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S
    (ResidueField S) Ideal.Quotient.mk_surjective x).mp (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ x
  simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  replace hx : x ∈ Ideal.map (algebraMap R S) (maximalIdeal R) := by simpa [H] using hx
  induction hx using Submodule.span_induction with
  | zero => simp
  | mem x h => obtain ⟨x, hx, rfl⟩ := h; simp
  | add x y hx hy _ _ => simp [*, TensorProduct.tmul_add]
  | smul a x hx _ =>
    have : residue S x = 0 := by rwa [residue_eq_zero_iff, ← H]
    simp [*, TensorProduct.tmul_add, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
/-
**Algebra.FormallyUnramified.iff_map_maximalIdeal_eq** 是 Mathlib 中的一个定理，位于命名空间 `
Algebra.FormallyUnramified`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [inst_3 : IsLocalRing R] [inst_4 : IsLocalRing S] [inst
_5 : IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S],   Algebra.Formall
yUnramified R S ↔     Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalR
ing.ResidueField S) ∧       Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal
 R) = IsLocalRing.maximalIdeal S
参数：algebraMap R S；IsLocalRing.ResidueField R；IsLocalRing.ResidueField S；algebraM
ap R S；IsLocalRing.maximalIdeal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.instIsSeparableResidueFieldOfFormallyUnramified`：∀ {R : Type u_1
} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S
]   [inst_3 : IsLocalRing R] [inst_4 : IsLoca…
· 使用定理 `Algebra.FormallyUnramified.map_maximalIdeal`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [inst_3 
: IsLocalRing R] [inst_4 : IsLoca…
· 使用定理 `Algebra.FormallyUnramified.of_map_maximalIdeal`：∀ {R : Type u_1} {S : Ty
pe u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [inst
_3 : IsLocalRing R] [inst_4 : IsLoca…
-/
lemma FormallyUnramified.iff_map_maximalIdeal_eq :
    Algebra.FormallyUnramified R S ↔
      Algebra.IsSeparable (ResidueField R) (ResidueField S) ∧
      (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
  ⟨fun _ ↦ ⟨inferInstance, map_maximalIdeal⟩, fun ⟨_, e⟩ ↦ of_map_maximalIdeal e⟩

end IsLocalRing

section IsUnramifiedAt

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [EssFiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
  [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

/-- Let `A` be an essentially of finite type `R`-algebra, `q` be a prime over `p`.
Then `A` is unramified at `p` if and only if `κ(q)/κ(p)` is separable, and `pS_q = qS_q`. -/
/-
**Algebra.isUnramifiedAt_iff_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：isUnramifiedAt_iff_map_eq : Algebra.IsUnramifiedAt R q ↔ Algebra.IsSeparab
le p.ResidueField q.ResidueField ∧ p.map (algebraMap R (Localization.AtPrime q))
 = maximalIdeal _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.EssFiniteType.of_comp`：∀ (R : Type u_1) (S : Type u_2) (T : Type
 u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   [inst_3 
: Algebra R S] [ins…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Algebra.instEssFiniteTypeLocalization`：∀ (R : Type u_1) (S : Type u_2) [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssFi
niteType R S] (M : Submonoi…
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Algebra.FormallyUnramified.of_restrictScalars`：of_restrictScalars [Forma
llyUnramified R B] : FormallyUnramified A B
· 使用定理 `Algebra.FormallyUnramified.comp`：comp [FormallyUnramified R A] [Formally
Unramified A B] : FormallyUnramified R B
· 使用定理 `Algebra.FormallyUnramified.instLocalization`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.FormallyUnramified R S] (M : Sub…
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.inst`：∀ {R : Type u} [inst : CommRing R], Algebra.Etale R 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`：∀ {R : Type u_1} {S 
: Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [
inst_3 : IsLocalRing R] [inst_4 : IsLoca…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq`：∀ {A : Type u_4} {
B : Type u_5} {inst : CommSemiring A} {inst_1 : CommSemiring B} {inst_2 : Algebr
a A B} {p : Ideal A}   {inst_3 : p.IsPrime…
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `Localization.localRingHom.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R]
 {P : Type u_3} [inst_1 : CommSemiring P] (I : Ideal R) [hI : I.IsPrime]   (J : 
Ideal P) [inst_2 : J…
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Let `A` be an essentially of finite type `R`-algebra, `q` be a prime over `p`.
Then `A` is unramified at `p` if and only if `κ(q)/κ(p)` is separable, and `pS_q
 = qS_q`.
-/
lemma isUnramifiedAt_iff_map_eq :
    Algebra.IsUnramifiedAt R q ↔
      Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal _ := by
  have : EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp R _ _
  trans Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q)
  · exact ⟨fun _ ↦ .of_restrictScalars R _ _,
      fun _ ↦ Algebra.FormallyUnramified.comp _ (Localization.AtPrime p) _⟩
  rw [FormallyUnramified.iff_map_maximalIdeal_eq]
  congr!
  rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Localization.localRingHom,
    IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsUnramifiedAt R q] : Algebra.IsSeparable p.ResidueField q.ResidueField :=
  ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.IsUnramifiedAt R q] : Module.Finite p.ResidueField q.ResidueField :=
  Algebra.FormallyUnramified.finite_of_free _ _

end IsUnramifiedAt

end Algebra

section UniquePrimeOver

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R} [p.IsPrime]
  {q : Ideal S} [q.IsPrime] (hq : p.primesOver S = {q})

include hq

namespace Localization

/-
**Localization.localRingHom_injective_of_primesOver_eq_singleton** 是 Mathlib 中的一
个引理，位于命名空间 `Localization`。
形式化陈述：localRingHom_injective_of_primesOver_eq_singleton [Algebra.IsIntegral R S]
 [FaithfulSMul R S] : Function.Injective (localRingHom p q (algebraMap R S) (hq.
ge rfl).2.1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Localization.le_comap_primeCompl_iff`：le_comap_primeCompl_iff {J : Ideal
 P} [J.IsPrime] {f : R ->+* P} : I.primeCompl <= J.primeCompl.comap f ↔ J.comap 
f <= I
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Localization.localRingHom_mk'`：localRingHom_mk' (J : Ideal P) [J.IsPrime
] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom
 I J f hIJ (IsLocal…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton`：exists_no
tMem_dvd_algebraMap_of_primesOver_eq_singleton {p : Ideal R} [p.IsPrime] {q : Id
eal S} [q.IsPrime] (hq : p.primesOver S = {q}) [Alg…
· 使用定理 `IsLocalization.mk'_eq_zero_iff`：∀ {R : Type u_1} [inst : CommSemiring R]
 {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra 
R S] [inst_3 : IsLoc…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
lemma localRingHom_injective_of_primesOver_eq_singleton
    [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    Function.Injective (localRingHom p q (algebraMap R S) (hq.ge rfl).2.1) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
  obtain ⟨a, haq, e⟩ : ∃ a ∉ q, a * (algebraMap R S) x = 0 := by
    simpa [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] using hx
  obtain ⟨r, hrp, t, e'⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ haq
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr
    ⟨⟨r, hrp⟩, FaithfulSMul.algebraMap_injective R S ?_⟩
  grind
/-
**Localization.finite_of_primesOver_eq_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Loca
lization`。
形式化陈述：finite_of_primesOver_eq_singleton [Module.Finite R S] [q.LiesOver p] [Alge
bra (Localization.AtPrime p) (Localization.AtPrime q)] [Localization.AtPrime.IsL
iesOverAlgebra p q] : Module.Finite (Localization.AtPrime p) (Localization.AtPri
me q)
参数：Localization.AtPrime p；Localization.AtPrime q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用引理 `AlgHom.coe_toLinearMap`：coe_toLinearMap : ⇑φ.toLinearMap = φ
· 使用定理 `IsScalarTower.coe_toAlgHom'`：coe_toAlgHom' : (toAlgHom R S A : S -> A) =
 algebraMap S A
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用引理 `Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton`：exists_no
tMem_dvd_algebraMap_of_primesOver_eq_singleton {p : Ideal R} [p.IsPrime] {q : Id
eal S} [q.IsPrime] (hq : p.primesOver S = {q}) [Alg…
· 使用引理 `Submodule.smul_mem_iff_of_isUnit`：smul_mem_iff_of_isUnit (hr : IsUnit r)
 : r • x in p ↔ x in p
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `IsLocalization.mk'_spec'_mk`：∀ {R : Type u_1} [inst : CommSemiring R] {M
 : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S
] [inst_3 : IsLoc…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
lemma finite_of_primesOver_eq_singleton [Module.Finite R S] [q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Module.Finite (Localization.AtPrime p) (Localization.AtPrime q) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨s.image (IsScalarTower.toAlgHom R _ _).toLinearMap, ?_⟩
  rw [Finset.coe_image, ← Submodule.span_span_of_tower R, ← Submodule.map_span, hs,
    Submodule.map_top, LinearMap.coe_range, AlgHom.coe_toLinearMap, IsScalarTower.coe_toAlgHom',
    ← top_le_iff]
  rintro x -
  obtain ⟨x, ⟨s, hsq⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  obtain ⟨r, hr, t, e'⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hsq
  rw [← Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units (M := p.primeCompl) _ ⟨r, hr⟩),
    Algebra.smul_def, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply _ S, e',
      map_mul, mul_assoc, mul_left_comm, IsLocalization.mk'_spec'_mk, ← map_mul]
  exact Submodule.subset_span ⟨_, rfl⟩
/-
**Localization.localRingHom_surjective_of_primesOver_eq_singleton** 是 Mathlib 中的
一个引理，位于命名空间 `Localization`。
形式化陈述：localRingHom_surjective_of_primesOver_eq_singleton [Module.Finite R S] [q.
LiesOver p] [Algebra.IsUnramifiedAt R q] [Algebra (Localization.AtPrime p) (Loca
lization.AtPrime q)] [Localization.AtPrime.IsLiesOverAlgebra p q] (H : Function.
Surjective (algebraMap p.ResidueField q.ResidueField)) : Function.Surjective (lo
calRingHom p q (algebraMap R S) (q.over_def p))
参数：Localization.AtPrime p；Localization.AtPrime q；H : Function.Surjective (algebr
aMap p.ResidueField q.ResidueField)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用引理 `Localization.finite_of_primesOver_eq_singleton`：finite_of_primesOver_eq_
singleton [Module.Finite R S] [q.LiesOver p] [Algebra (Localization.AtPrime p) (
Localization.AtPrime q)] [Localizati…
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq`：∀ {A : Type u_4} {
B : Type u_5} {inst : CommSemiring A} {inst_1 : CommSemiring B} {inst_2 : Algebr
a A B} {p : Ideal A}   {inst_3 : p.IsPrime…
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Submodule.le_of_le_smul_of_le_jacobson_bot`：le_of_le_smul_of_le_jacobson
_bot {R M} [CommRing R] [AddCommGroup M] [Module R M] {I : Ideal R} {N N' : Subm
odule R M} (hN' : N'.FG) (hIJ : …
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `IsLocalRing.maximalIdeal_le_jacobson`：maximalIdeal_le_jacobson (I : Idea
l R) : IsLocalRing.maximalIdeal R <= I.jacobson
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
· 使用定理 `Algebra.FormallyUnramified.map_maximalIdeal`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [inst_3 
: IsLocalRing R] [inst_4 : IsLoca…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
· 使用定理 `Algebra.instFormallyUnramifiedAtPrimeOfIsUnramifiedAtOfIsLiesOverAlgebra
`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A] (p : Ideal R)   [inst_3 : p.IsPrime] (q : I…
· 使用引理 `IsLocalRing.residue_surjective`：residue_surjective : Function.Surjective
 (IsLocalRing.residue R)
· 使用定理 `sub_sub_self`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - (a
 - b) = b
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用引理 `IsLocalRing.residue_eq_zero_iff`：residue_eq_zero_iff (x : R) : residue R
 x = 0 ↔ x in maximalIdeal R
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `IsLocalRing.ResidueField.algebraMap_eq`：∀ (R : Type u_1) [inst : CommRin
g R] [inst_1 : IsLocalRing R],   algebraMap R (IsLocalRing.ResidueField R) = IsL
ocalRing.residue R
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
（共 32 条，此处仅展示前 30 条）
-/
lemma localRingHom_surjective_of_primesOver_eq_singleton
    [Module.Finite R S] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    (H : Function.Surjective (algebraMap p.ResidueField q.ResidueField)) :
    Function.Surjective (localRingHom p q (algebraMap R S) (q.over_def p)) := by
  have := Localization.finite_of_primesOver_eq_singleton hq
  rw [← Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
  change Function.Surjective (Algebra.linearMap _ _)
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson _)
  rw [Ideal.smul_top_eq_map, Algebra.FormallyUnramified.map_maximalIdeal]
  rintro x -
  obtain ⟨a, ha⟩ := H (algebraMap _ _ x)
  obtain ⟨a, rfl⟩ := residue_surjective a
  rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply _ (Localization.AtPrime q), ResidueField.algebraMap_eq,
    ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at ha
  rw [← sub_sub_self (algebraMap _ _ a) x]
  refine sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ha)

omit hq in
/-
**Localization.exists_awayMap_injective_of_localRingHom_injective** 是 Mathlib 中的
一个引理，位于命名空间 `Localization`。
形式化陈述：exists_awayMap_injective_of_localRingHom_injective (hRS : (RingHom.ker (al
gebraMap R S)).FG) [q.LiesOver p] (H : Function.Injective (localRingHom p q (alg
ebraMap R S) (q.over_def p))) : exists r ∉ p, forall r', r ∣ r' -> Function.Inje
ctive (awayMap (algebraMap R S) r')
参数：hRS : (RingHom.ker (algebraMap R S)).FG；H : Function.Injective (localRingHom 
p q (algebraMap R S) (q.over_def p))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Fintype.prod_eq_mul_prod_compl`：∀ {ι : Type u_1} {M : Type u_3} [inst : 
CommMonoid M] [inst_1 : DecidableEq ι] [inst_2 : Fintype ι] (a : ι) (f : ι → M),
   ∏ i, f i = f a * …
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 37 条，此处仅展示前 30 条）
-/
lemma exists_awayMap_injective_of_localRingHom_injective
    (hRS : (RingHom.ker (algebraMap R S)).FG) [q.LiesOver p]
    (H : Function.Injective (localRingHom p q (algebraMap R S) (q.over_def p))) :
    ∃ r ∉ p, ∀ r', r ∣ r' → Function.Injective (awayMap (algebraMap R S) r') := by
  classical
  obtain ⟨s, hs⟩ := hRS
  have (x : s) : algebraMap R (Localization.AtPrime p) x.1 = 0 := by
    apply H
    simp [localRingHom_to_map, -FaithfulSMul.algebraMap_eq_zero_iff,
      show algebraMap R S _ = 0 from hs.le (Ideal.subset_span x.2)]
  choose m hm using fun x ↦ (IsLocalization.map_eq_zero_iff p.primeCompl _ _).mp (this x)
  have H : RingHom.ker (algebraMap R S) ≤ RingHom.ker
      (algebraMap R (Localization.Away (∏ i, m i).1)) := by
    rw [← hs, Ideal.span_le]
    intro x hxs
    refine (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mpr ⟨⟨_, 1, rfl⟩, ?_⟩
    simp only [pow_one]
    rw [Fintype.prod_eq_mul_prod_compl ⟨x, hxs⟩, Submonoid.coe_mul, mul_assoc, mul_left_comm, hm,
      mul_zero]
  refine ⟨_, (∏ i : s, m i).2, ?_⟩
  rintro r' ⟨s, e⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, _, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r') x
  simp only [awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hx
  simp only [← map_pow, ← map_mul] at hn
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (.powers (∏ i, m i).1) _ _).mp (H hn)
  refine (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨_, k + n, rfl⟩, ?_⟩
  dsimp only at hk ⊢
  rw [pow_add, mul_assoc, e, mul_pow, ← e, mul_assoc, mul_left_comm, hk, mul_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**Localization.exists_awayMap_bijective_of_localRingHom_bijective** 是 Mathlib 中的
一个引理，位于命名空间 `Localization`。
形式化陈述：exists_awayMap_bijective_of_localRingHom_bijective [Module.Finite R S] [q.
LiesOver p] (hRS : (RingHom.ker (algebraMap R S)).FG) (H : Function.Bijective (l
ocalRingHom p q (algebraMap R S) (q.over_def p))) : exists r ∉ p, forall r', r ∣
 r' -> Function.Bijective (awayMap (algebraMap R S) r')
参数：hRS : (RingHom.ker (algebraMap R S)).FG；H : Function.Bijective (localRingHom 
p q (algebraMap R S) (q.over_def p))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `IsLocalization.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Localization.le_comap_primeCompl_iff`：le_comap_primeCompl_iff {J : Ideal
 P} [J.IsPrime] {f : R ->+* P} : I.primeCompl <= J.primeCompl.comap f ↔ J.comap 
f <= I
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Localization.localRingHom_mk'`：localRingHom_mk' (J : Ideal P) [J.IsPrime
] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom
 I J f hIJ (IsLocal…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton`：exists_no
tMem_dvd_algebraMap_of_primesOver_eq_singleton {p : Ideal R} [p.IsPrime] {q : Id
eal S} [q.IsPrime] (hq : p.primesOver S = {q}) [Alg…
· 使用定理 `Ideal.IsPrime.mul_notMem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x ∉ I → y ∉ I → x * y ∉ I
· 使用引理 `Localization.exists_awayMap_injective_of_localRingHom_injective`：exists_
awayMap_injective_of_localRingHom_injective (hRS : (RingHom.ker (algebraMap R S)
).FG) [q.LiesOver p] (H : Function.Injective (localRi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
（共 75 条，此处仅展示前 30 条）
-/
lemma exists_awayMap_bijective_of_localRingHom_bijective
    [Module.Finite R S] [q.LiesOver p] (hRS : (RingHom.ker (algebraMap R S)).FG)
    (H : Function.Bijective (localRingHom p q (algebraMap R S) (q.over_def p))) :
    ∃ r ∉ p, ∀ r', r ∣ r' → Function.Bijective (awayMap (algebraMap R S) r') := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  have (x : S) : ∃ a, ∃ b ∉ p, algebraMap R S a = x * algebraMap R S b := by
    have := (IsLocalization.mk'_surjective p.primeCompl).exists.mp (H.2 (algebraMap _ _ x))
    simp only [localRingHom_mk', Prod.exists, Subtype.exists, Ideal.mem_primeCompl_iff,
      IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at this
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := this
    obtain ⟨d, hd, e, he⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hq _ hcq
    exact ⟨d * a, d * b, ‹p.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp e using this
  obtain ⟨r, hrp, hr⟩ := Localization.exists_awayMap_injective_of_localRingHom_injective hRS H.1
  refine ⟨r * ∏ i ∈ s, b i, mul_mem (s := p.primeCompl) hrp (prod_mem fun _ _ ↦ hbp _), ?_⟩
  refine fun r' hr' ↦ ⟨hr _ (.trans ⟨_, rfl⟩ hr'), ?_⟩
  have H : (IsScalarTower.toAlgHom R S _).range ≤ (awayMapₐ (Algebra.ofId R S) r').range := by
    rw [← Algebra.map_top, Subalgebra.map_le, ← hs, Algebra.adjoin_le_iff]
    intro x hxs
    obtain ⟨r'', hr'⟩ := hr'
    refine ⟨IsLocalization.mk' (M := .powers r') _
      (r'' * r * (∏ i ∈ s.erase x, b i) * a x) ⟨_, 1, rfl⟩, ?_⟩
    dsimp [awayMapₐ, IsLocalization.Away.map]
    simp only [pow_one, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul,
      ← map_mul (algebraMap S _), map_mul (algebraMap R _), e]
    congr 1
    rw [hr', ← Finset.prod_erase_mul s b hxs, map_mul, map_mul, map_mul]
    ring_nf
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers (algebraMap R S r')) x
  obtain ⟨y, hy : awayMap _ _ _ = _⟩ := H ⟨x, rfl⟩
  dsimp at hy
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, hy]
  simp [Away.invSelf, Localization.mk_eq_mk', awayMap, IsLocalization.Away.map,
    IsLocalization.map_mk', ← Algebra.smul_def, IsLocalization.smul_mk', ← IsLocalization.mk'_pow]
/-
**Localization.exists_awayMap_bijective_of_residueField_surjective** 是 Mathlib 中
的一个引理，位于命名空间 `Localization`。
形式化陈述：exists_awayMap_bijective_of_residueField_surjective [Module.Finite R S] [F
aithfulSMul R S] [q.LiesOver p] [Algebra.IsUnramifiedAt R q] [Algebra (Localizat
ion.AtPrime p) (Localization.AtPrime q)] [Localization.AtPrime.IsLiesOverAlgebra
 p q] (H : Function.Surjective (algebraMap p.ResidueField q.ResidueField)) : exi
sts r ∉ p, forall r', r ∣ r' -> Function.Bijective (awayMap (algebraMap R S) r')
参数：Localization.AtPrime p；Localization.AtPrime q；H : Function.Surjective (algebr
aMap p.ResidueField q.ResidueField)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用引理 `Localization.exists_awayMap_bijective_of_localRingHom_bijective`：exists_
awayMap_bijective_of_localRingHom_bijective [Module.Finite R S] [q.LiesOver p] (
hRS : (RingHom.ker (algebraMap R S)).FG) (H : Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FaithfulSMul.ker_algebraMap_eq_bot`：FaithfulSMul.ker_algebraMap_eq_bot (
R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A] : Ri
ngHom.ker (algebraMap R …
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用引理 `Localization.localRingHom_injective_of_primesOver_eq_singleton`：localRin
gHom_injective_of_primesOver_eq_singleton [Algebra.IsIntegral R S] [FaithfulSMul
 R S] : Function.Injective (localRingHom p q (algebr…
· 使用引理 `Localization.localRingHom_surjective_of_primesOver_eq_singleton`：localRi
ngHom_surjective_of_primesOver_eq_singleton [Module.Finite R S] [q.LiesOver p] [
Algebra.IsUnramifiedAt R q] [Algebra (Localization.At…
-/
lemma exists_awayMap_bijective_of_residueField_surjective
    [Module.Finite R S] [FaithfulSMul R S] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    (H : Function.Surjective (algebraMap p.ResidueField q.ResidueField)) :
    ∃ r ∉ p, ∀ r', r ∣ r' → Function.Bijective (awayMap (algebraMap R S) r') :=
  exists_awayMap_bijective_of_localRingHom_bijective hq (by simpa using! Submodule.fg_bot)
    ⟨localRingHom_injective_of_primesOver_eq_singleton hq,
      localRingHom_surjective_of_primesOver_eq_singleton hq H⟩

end Localization

end UniquePrimeOver

