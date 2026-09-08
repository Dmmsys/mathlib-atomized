/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.PrincipalIdealDomain

/-!

# Bézout rings

A Bézout ring (Bezout ring) is a ring whose finitely generated ideals are principal.
Notable examples include principal ideal rings, valuation rings, and the ring of algebraic integers.

## Main results
- `IsBezout.iff_span_pair_isPrincipal`: It suffices to verify every `span {x, y}` is principal.
- `IsBezout.TFAE`: For a Bézout domain, Noetherian ↔ PID ↔ UFD ↔ ACCP

-/

public section


universe u v

variable {R : Type u} [CommRing R]

namespace IsBezout

/-
**IsBezout.iff_span_pair_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 `IsBezout`。
形式化陈述：iff_span_pair_isPrincipal : IsBezout R ↔ forall x y : R, (Ideal.span {x, y
} : Ideal R).IsPrincipal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_induction`：fg_induction {R M : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] {motive : forall N : Submodule R M, N.FG -> Prop} (single
ton : forall…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_insert`：span_insert (x) (s : Set M) : span R (insert x s)
 = R ∙ x ⊔ span R s
-/
theorem iff_span_pair_isPrincipal :
    IsBezout R ↔ ∀ x y : R, (Ideal.span {x, y} : Ideal R).IsPrincipal := by
  constructor
  · intro H x y; infer_instance
  · intro H
    constructor
    apply Submodule.fg_induction
    · exact fun _ => ⟨⟨_, rfl⟩⟩
    · rintro _ _ _ _ ⟨⟨x, rfl⟩⟩ ⟨⟨y, rfl⟩⟩
      rw [← Submodule.span_insert]
      exact H _ _
/-
**IsBezout._root_.Function.Surjective.isBezout** 是 Mathlib 中的一个定理，位于命名空间 `IsBezo
ut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Surjective.isBezout {S : Type v} [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) [IsBezout R] : IsBezout S := by
  rw [iff_span_pair_isPrincipal]
  intro x y
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hf x, hf y
  use f (gcd x y)
  trans Ideal.map f (Ideal.span {gcd x y})
  · rw [span_gcd, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  · rw [Ideal.map_span, Set.image_singleton]

set_option backward.isDefEq.respectTransparency false in
/-
**IsBezout.TFAE** 是 Mathlib 中的一个定理，位于命名空间 `IsBezout`。
形式化陈述：TFAE [IsBezout R] [IsDomain R] : List.TFAE [IsNoetherianRing R, IsPrincipa
lIdealRing R, UniqueFactorizationMonoid R, WfDvdMonoid R]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout`：∀ {R : Type u} [in
st : Semiring R] [IsNoetherianRing R] [IsBezout R], IsPrincipalIdealRing R
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isNoetherianRing_iff`：isNoetherianRing_iff {R} [Semiring R] : IsNoetheri
anRing R ↔ IsNoetherian R R
· 使用定理 `isNoetherian_iff_fg_wellFounded`：isNoetherian_iff_fg_wellFounded : IsNoe
therian R M ↔ WellFoundedGT { N : Submodule R M // N.FG }
· 使用定理 `RelEmbedding.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s), WellFounded s → WellFounded r
· 使用定理 `Submodule.IsPrincipal.principal`：∀ {R : Type u_1} {M : Type u_4} {inst :
 Semiring R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   (S : Subm
odule R M) [self : S.…
· 使用定理 `IsBezout.isPrincipal_of_FG`：∀ {R : Type u} {inst : Semiring R} [self : I
sBezout R] (I : Ideal R), I.FG → Submodule.IsPrincipal I
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_lt_span_singleton`：span_singleton_lt_span_singleton
 [IsDomain α] {x y : α} : span ({x} : Set α) < span ({y} : Set α) ↔ DvdNotUnit y
 x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
-/
theorem TFAE [IsBezout R] [IsDomain R] :
    List.TFAE
    [IsNoetherianRing R, IsPrincipalIdealRing R, UniqueFactorizationMonoid R, WfDvdMonoid R] := by
  tfae_have 1 → 2
  | _ => inferInstance
  tfae_have 2 → 3
  | _ => inferInstance
  tfae_have 3 → 4
  | _ => inferInstance
  tfae_have 4 → 1
  | ⟨h⟩ => by
    rw [isNoetherianRing_iff, isNoetherian_iff_fg_wellFounded]
    refine ⟨RelEmbedding.wellFounded ?_ h⟩
    have : ∀ I : { J : Ideal R // J.FG }, ∃ x : R, (I : Ideal R) = Ideal.span {x} :=
      fun ⟨I, hI⟩ => (IsBezout.isPrincipal_of_FG I hI).1
    choose f hf using this
    exact
      { toFun := f
        inj' := fun x y e => by ext1; rw [hf, hf, e]
        map_rel_iff' := by
          dsimp
          intro a b
          rw [← Ideal.span_singleton_lt_span_singleton, ← hf, ← hf]
          rfl }
  tfae_finish

end IsBezout

