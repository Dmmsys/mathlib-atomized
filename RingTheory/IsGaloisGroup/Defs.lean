/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Invariant.Defs

/-!
# Predicate for Galois Groups

Given an action of a group `G` on an extension of fields `L/K`, we introduce a predicate
`IsGaloisGroup G K L` saying that `G` acts faithfully on `L` with fixed field `K`. In particular,
we do not assume that `L` is an algebraic extension of `K`.

## Implementation notes

We actually define `IsGaloisGroup G A B` for extensions of rings `B/A`, with the same definition
(faithful action on `B` with fixed ring `A`). This definition turns out to axiomatize a common
setup in algebraic number theory where a Galois group `Gal(L/K)` acts on an extension of subrings
`B/A` (e.g., rings of integers). In particular, there are theorems in algebraic number theory that
naturally assume `[IsGaloisGroup G A B]` and whose statements would otherwise require assuming
`(K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]` (along with predicates relating
`K` and `L` to the rings `A` and `B`) despite `K` and `L` not appearing in the conclusion.

Unfortunately, this definition of `IsGaloisGroup G A B` for extensions of rings `B/A` is
nonstandard and clashes with other notions such as the étale fundamental group. In particular, if
`G` is finite and `A` is integrally closed, then  `IsGaloisGroup G A B` is equivalent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with Galois group `G`
(see `IsGaloisGroup.iff_isFractionRing`), rather than `B/A` being étale for instance.

But in the absence of a more suitable name, the utility of the predicate `IsGaloisGroup G A B` for
extensions of rings `B/A` seems to outweigh these terminological issues.
-/

@[expose] public section

assert_not_exists IsFractionRing

variable (G A A' B : Type*) [Group G] [CommSemiring A] [Semiring B] [Algebra A B]
  [MulSemiringAction G B]

/-- `G` is a Galois group for `L/K` if the action of `G` on `L` is faithful with fixed field `K`.
In particular, we do not assume that `L` is an algebraic extension of `K`.

See the implementation notes in this file for the meaning of this definition in the case of rings.
-/
/-
**IsGaloisGroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) →   (A : Type u_2) →     (B : Type u_4) →       [inst : Gro
up G] →         [inst_1 : CommSemiring A] → [inst_2 : Semiring B] → [Algebra A B
] → [MulSemiringAction G B] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G` is a Galois group for `L/K` if the action of `G` on `L` is faithful with fix
ed field `K`.
In particular, we do not assume that `L` is an algebraic extension of `K`.

See the implementation notes in this file for the meaning of this definition in 
the case of rings.
-/
class IsGaloisGroup where
  faithful : FaithfulSMul G B
  commutes : SMulCommClass G A B
  isInvariant : Algebra.IsInvariant A B G

namespace IsGaloisGroup

variable {G A B} in
/-
**IsGaloisGroup.of_mulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：of_mulEquiv [hG : IsGaloisGroup G A B] {H : Type*} [Group H] [MulSemiringA
ction H B] (e : H ≃* G) (he : forall h (x : B), (e h) • x = h • x) : IsGaloisGro
up H A B where faithful
参数：e : H ≃* G；he : forall h (x : B), (e h) • x = h • x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `IsGaloisGroup.faithful`：∀ {G : Type u_1} (A : Type u_2) {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
-/
theorem of_mulEquiv [hG : IsGaloisGroup G A B] {H : Type*} [Group H]
    [MulSemiringAction H B] (e : H ≃* G) (he : ∀ h (x : B), (e h) • x = h • x) :
    IsGaloisGroup H A B where
  faithful := ⟨fun h ↦ e.injective <| hG.faithful.eq_of_smul_eq_smul <| by simpa only [he]⟩
  commutes := ⟨fun x a b ↦ by simpa [he] using hG.commutes.smul_comm (e x) a b⟩
  isInvariant := ⟨fun b h ↦
    have he' : ∀ (g : G) (x : B), e.symm g • x = g • x := fun g x ↦ by simp [← he]
    hG.isInvariant.isInvariant b (fun g ↦ by simpa [he'] using h (e.symm g))⟩

variable {G A B} in
/-
**IsGaloisGroup.iff_of_mulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：iff_of_mulEquiv {H : Type*} [Group H] [MulSemiringAction H B] (e : H ≃* G)
 (he : forall h (x : B), e h • x = h • x) : IsGaloisGroup H A B ↔ IsGaloisGroup 
G A B
参数：e : H ≃* G；he : forall h (x : B), e h • x = h • x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.of_mulEquiv`：of_mulEquiv [hG : IsGaloisGroup G A B] {H : T
ype*} [Group H] [MulSemiringAction H B] (e : H ≃* G) (he : forall h (x : B), (e 
h) • x = h • x)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem iff_of_mulEquiv {H : Type*} [Group H] [MulSemiringAction H B]
    (e : H ≃* G) (he : ∀ h (x : B), e h • x = h • x) :
    IsGaloisGroup H A B ↔ IsGaloisGroup G A B := by
  refine ⟨fun h ↦ h.of_mulEquiv e.symm fun g x ↦ ?_, fun h ↦ h.of_mulEquiv e he⟩
  rw [← he, e.apply_symm_apply]

variable {G A B} in
@[simp]
/-
**IsGaloisGroup.top_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：top_iff : IsGaloisGroup (⊤ : Subgroup G) A B ↔ IsGaloisGroup G A B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.iff_of_mulEquiv`：iff_of_mulEquiv {H : Type*} [Group H] [Mu
lSemiringAction H B] (e : H ≃* G) (he : forall h (x : B), e h • x = h • x) : IsG
aloisGroup H A B ↔ …
-/
theorem top_iff : IsGaloisGroup (⊤ : Subgroup G) A B ↔ IsGaloisGroup G A B :=
  iff_of_mulEquiv Subgroup.topEquiv fun _ _ ↦ rfl
/-
**IsGaloisGroup.** 是 Mathlib 中的一个实例，位于命名空间 `IsGaloisGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsGaloisGroup G A B] : IsGaloisGroup (⊤ : Subgroup G) A B :=
  IsGaloisGroup.top_iff.mpr ‹_›
/-
**IsGaloisGroup.of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：of_algEquiv [hG : IsGaloisGroup G A B] (B' : Type*) [Semiring B'] [Algebra
 A B'] [MulSemiringAction G B'] (e : B ≃ₐ[A] B') (he : forall (g : G) (x : B), e
 (g • x) = g • (e x)) : IsGaloisGroup G A B' where faithful
参数：B' : Type*；e : B ≃ₐ[A] B'；he : forall (g : G) (x : B), e (g • x) = g • (e x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `IsGaloisGroup.faithful`：∀ {G : Type u_1} (A : Type u_2) {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
-/
theorem of_algEquiv [hG : IsGaloisGroup G A B] (B' : Type*) [Semiring B']
    [Algebra A B'] [MulSemiringAction G B'] (e : B ≃ₐ[A] B')
    (he : ∀ (g : G) (x : B), e (g • x) = g • (e x)) :
    IsGaloisGroup G A B' where
  faithful := ⟨fun h ↦ hG.faithful.eq_of_smul_eq_smul fun b ↦ by simpa [← he] using h (e b)⟩
  commutes := ⟨fun g a b' ↦ by
    have h' {x'} : e.symm (g • x') = g • e.symm x' := by
      apply e.injective
      simp [he]
    apply e.symm.injective
    simpa [h', map_smul] using hG.commutes.smul_comm g a (e.symm b')⟩
  isInvariant := ⟨fun x' hx' ↦ by
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant (e.symm x') (fun g ↦ by
      apply e.injective
      simp [he, hx'])
    exact ⟨a, by rw [← e.commutes, ha, AlgEquiv.apply_symm_apply]⟩⟩
/-
**IsGaloisGroup.of_ringHom_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：of_ringHom_surjective [hG : IsGaloisGroup G A B] [CommSemiring A'] [Algebr
a A' B] (e : A ->+* A') (he : forall a, algebraMap A' B (e a) = algebraMap A B a
) (he' : Function.Surjective e) : IsGaloisGroup G A' B where faithful
参数：e : A ->+* A'；he : forall a, algebraMap A' B (e a) = algebraMap A B a；he' : F
unction.Surjective e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.faithful`：∀ {G : Type u_1} (A : Type u_2) {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsGaloisGroup.commutes`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4} {
inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : Alge
bra A B} {in…
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
-/
theorem of_ringHom_surjective [hG : IsGaloisGroup G A B] [CommSemiring A']
    [Algebra A' B] (e : A →+* A') (he : ∀ a, algebraMap A' B (e a) = algebraMap A B a)
    (he' : Function.Surjective e) : IsGaloisGroup G A' B where
  faithful := hG.faithful
  commutes := ⟨by
    intro g a' b
    obtain ⟨a, rfl⟩ : ∃ a, e a = a' := he' a'
    rw [Algebra.smul_def, Algebra.smul_def, he, ← Algebra.smul_def, ← Algebra.smul_def]
    exact hG.commutes.smul_comm g a b⟩
  isInvariant := ⟨by
    intro b h
    obtain ⟨a, ha⟩ := hG.isInvariant.isInvariant b h
    exact ⟨e a, by rw [he, ha]⟩⟩
/-
**IsGaloisGroup.of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGroup`。
形式化陈述：of_ringEquiv [hG : IsGaloisGroup G A B] [CommSemiring A'] [Algebra A' B] (
e : A ≃+* A') (he : forall a, algebraMap A' B (e a) = algebraMap A B a) : IsGalo
isGroup G A' B
参数：e : A ≃+* A'；he : forall a, algebraMap A' B (e a) = algebraMap A B a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.of_ringHom_surjective`：of_ringHom_surjective [hG : IsGaloi
sGroup G A B] [CommSemiring A'] [Algebra A' B] (e : A ->+* A') (he : forall a, a
lgebraMap A' B (e a) = al…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
-/
theorem of_ringEquiv [hG : IsGaloisGroup G A B] [CommSemiring A'] [Algebra A' B]
    (e : A ≃+* A') (he : ∀ a, algebraMap A' B (e a) = algebraMap A B a) :
    IsGaloisGroup G A' B :=
  .of_ringHom_surjective G A A' B e he e.surjective

attribute [instance low] IsGaloisGroup.commutes IsGaloisGroup.isInvariant

variable [hA : IsGaloisGroup G A B] [FaithfulSMul A B]

/-- If `B/A` is Galois with Galois group `G`, then `A` is isomorphic to the subring of elements of
`B` fixed by `G`. -/
@[simps apply_coe]
/-
**IsGaloisGroup.ringEquivFixedPoints** 是 Mathlib 中的一个定义，位于命名空间 `IsGaloisGroup`。
形式化陈述：ringEquivFixedPoints : A ≃+* FixedPoints.subsemiring B G where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `B/A` is Galois with Galois group `G`, then `A` is isomorphic to the subring 
of elements of
`B` fixed by `G`.
-/
noncomputable def ringEquivFixedPoints :
    A ≃+* FixedPoints.subsemiring B G where
  toFun x := ⟨algebraMap A B x, fun _ ↦ by rw [smul_algebraMap]⟩
  invFun x := (hA.isInvariant.isInvariant x x.prop).choose
  map_mul' _ _ := by simp [Subtype.ext_iff]
  map_add' _ _ := by simp [Subtype.ext_iff]
  left_inv _ := by simp
  right_inv x := by simpa [Subtype.ext_iff] using (hA.isInvariant.isInvariant x x.prop).choose_spec

@[simp]
/-
**IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply** 是 Mathlib 中的一个定理，位于
命名空间 `IsGaloisGroup`。
形式化陈述：algebraMap_ringEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B 
G) : algebraMap A B ((ringEquivFixedPoints G A B).symm x) = x
参数：x : FixedPoints.subsemiring B G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Algebra.IsInvariant.isInvariant`：∀ {A : Type u_1} {B : Type u_2} {G : Ty
pe u_3} {inst : CommSemiring A} {inst_1 : Semiring B} {inst_2 : Algebra A B}   {
inst_3 : Group G} {in…
· 使用定理 `IsGaloisGroup.isInvariant`：∀ {G : Type u_1} {A : Type u_2} {B : Type u_4
} {inst : Group G} {inst_1 : CommSemiring A} {inst_2 : Semiring B}   {inst_3 : A
lgebra A B} {in…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem algebraMap_ringEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) :
    algebraMap A B ((ringEquivFixedPoints G A B).symm x) = x :=
 (hA.isInvariant.isInvariant x x.prop).choose_spec

variable [CommSemiring A'] [Algebra A' B] [FaithfulSMul A' B] [hA' : IsGaloisGroup G A' B]

/-- If `B/A` and `B/A'` are Galois with the same Galois group, then `A ≃+* A'`. -/
/-
**IsGaloisGroup.ringEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsGaloisGroup`。
形式化陈述：ringEquiv : A ≃+* A'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `B/A` and `B/A'` are Galois with the same Galois group, then `A ≃+* A'`.
-/
noncomputable def ringEquiv : A ≃+* A' :=
  (ringEquivFixedPoints G A B).trans (ringEquivFixedPoints G A' B).symm

@[simp]
/-
**IsGaloisGroup.algebraMap_ringEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsGaloisGr
oup`。
形式化陈述：algebraMap_ringEquiv_apply (x : A) : algebraMap A' B (IsGaloisGroup.ringEq
uiv G A A' B x) = algebraMap A B x
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply`：algebraMap_rin
gEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) : algebraMap A B 
((ringEquivFixedPoints G A B).symm x) = x
· 使用定理 `IsGaloisGroup.ringEquivFixedPoints_apply_coe`：∀ (G : Type u_1) (A : Type
 u_2) (B : Type u_4) [inst : Group G] [inst_1 : CommSemiring A] [inst_2 : Semiri
ng B]   [inst_3 : Algebra A B] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_ringEquiv_apply (x : A) :
    algebraMap A' B (IsGaloisGroup.ringEquiv G A A' B x) = algebraMap A B x := by
  simp [ringEquiv]

@[simp]
/-
**IsGaloisGroup.algebraMap_ringEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsGal
oisGroup`。
形式化陈述：algebraMap_ringEquiv_symm_apply (x : A') : algebraMap A B ((IsGaloisGroup.
ringEquiv G A A' B).symm x) = algebraMap A' B x
参数：x : A'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply`：algebraMap_rin
gEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) : algebraMap A B 
((ringEquivFixedPoints G A B).symm x) = x
· 使用定理 `IsGaloisGroup.ringEquivFixedPoints_apply_coe`：∀ (G : Type u_1) (A : Type
 u_2) (B : Type u_4) [inst : Group G] [inst_1 : CommSemiring A] [inst_2 : Semiri
ng B]   [inst_3 : Algebra A B] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_ringEquiv_symm_apply (x : A') :
    algebraMap A B ((IsGaloisGroup.ringEquiv G A A' B).symm x) = algebraMap A' B x := by
  simp [ringEquiv]

end IsGaloisGroup

