/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Morenikeji Neri
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain

/-!
# Principal ideal rings, principal ideal domains, and Bézout rings

A principal ideal ring (PIR) is a ring in which all left ideals are principal. A
principal ideal domain (PID) is an integral domain which is a principal ideal ring.

The definition of `IsPrincipalIdealRing` can be found in `Mathlib/RingTheory/Ideal/Span.lean`.

## Main definitions

Note that for principal ideal domains, one should use
`[IsDomain R] [IsPrincipalIdealRing R]`. There is no explicit definition of a PID.
Theorems about PID's are in the `PrincipalIdealRing` namespace.

- `IsBezout`: the predicate saying that every finitely generated left ideal is principal.
- `generator`: a generator of a principal ideal (or more generally submodule)
- `to_uniqueFactorizationMonoid`: a PID is a unique factorization domain

## Main results

- `Ideal.IsPrime.to_maximal_ideal`: a non-zero prime ideal in a PID is maximal.
- `EuclideanDomain.to_principal_ideal_domain` : a Euclidean domain is a PID.
- `IsBezout.nonemptyGCDMonoid`: Every Bézout domain is a GCD domain.

-/

@[expose] public section


universe u v

variable {R : Type u} {M : Type v}

open Set Function

open Submodule

section

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-
**bot_isPrincipal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：bot_isPrincipal : (⊥ : Submodule R M).IsPrincipal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance bot_isPrincipal : (⊥ : Submodule R M).IsPrincipal :=
  ⟨⟨0, by simp⟩⟩
/-
**top_isPrincipal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：top_isPrincipal : (⊤ : Submodule R R).IsPrincipal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
-/
instance top_isPrincipal : (⊤ : Submodule R R).IsPrincipal :=
  ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩

variable (R)

/-- A Bézout ring is a ring whose finitely generated ideals are principal. -/
/-
**IsBezout** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [Semiring R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Bézout ring is a ring whose finitely generated ideals are principal.
-/
class IsBezout : Prop where
  /-- Any finitely generated ideal is principal. -/
  isPrincipal_of_FG : ∀ I : Ideal R, I.FG → I.IsPrincipal
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsBezout.of_isPrincipalIdealRing [IsPrincipalIdealRing R] : IsBezout R :=
  ⟨fun I _ => IsPrincipalIdealRing.principal I⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DivisionSemiring.isPrincipalIdealRing (K : Type u) [DivisionSemiring K] :
    IsPrincipalIdealRing K where
  principal S := by
    rcases Ideal.eq_bot_or_top S with (rfl | rfl)
    · apply bot_isPrincipal
    · apply top_isPrincipal

end

namespace Submodule.IsPrincipal

variable [AddCommMonoid M]

section Semiring

variable [Semiring R] [Module R M]

@[simp]
/-
**Submodule.IsPrincipal._root_.Ideal.span_singleton_generator** 是 Mathlib 中的一个定理
，位于命名空间 `Submodule.IsPrincipal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ideal.span_singleton_generator (I : Ideal R) [I.IsPrincipal] :
    Ideal.span ({generator I} : Set R) = I :=
  Eq.symm (Classical.choose_spec (principal I))

@[simp]
/-
**Submodule.IsPrincipal.generator_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsPri
ncipal`。
形式化陈述：generator_mem (S : Submodule R M) [S.IsPrincipal] : generator S in S
参数：S : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsPrincipal.span_singleton_generator`：span_singleton_generator
 (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S
-/
theorem generator_mem (S : Submodule R M) [S.IsPrincipal] : generator S ∈ S := by
  have : generator S ∈ span R {generator S} := subset_span (mem_singleton _)
  convert! this
  exact span_singleton_generator S |>.symm
/-
**Submodule.IsPrincipal.mem_iff_eq_smul_generator** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module.IsPrincipal`。
形式化陈述：mem_iff_eq_smul_generator (S : Submodule R M) [S.IsPrincipal] {x : M} : x 
in S ↔ exists s : R, x = s • generator S
参数：S : Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.IsPrincipal.span_singleton_generator`：span_singleton_generator
 (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iff_eq_smul_generator (S : Submodule R M) [S.IsPrincipal] {x : M} :
    x ∈ S ↔ ∃ s : R, x = s • generator S := by
  simp_rw [@eq_comm _ x, ← mem_span_singleton, span_singleton_generator]
/-
**Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Submodule.IsPrincipal`。
形式化陈述：eq_bot_iff_generator_eq_zero (S : Submodule R M) [S.IsPrincipal] : S = ⊥ ↔
 generator S = 0
参数：S : Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_singleton_eq_bot`：span_singleton_eq_bot : R ∙ x = ⊥ ↔ x =
 0
· 使用定理 `Submodule.IsPrincipal.span_singleton_generator`：span_singleton_generator
 (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_bot_iff_generator_eq_zero (S : Submodule R M) [S.IsPrincipal] :
    S = ⊥ ↔ generator S = 0 := by rw [← @span_singleton_eq_bot R M, span_singleton_generator]

@[simp]
/-
**Submodule.IsPrincipal.generator_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsPri
ncipal`。
形式化陈述：generator_bot : generator (⊥ : Submodule R M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero`：eq_bot_iff_generator
_eq_zero (S : Submodule R M) [S.IsPrincipal] : S = ⊥ ↔ generator S = 0
-/
theorem generator_bot : generator (⊥ : Submodule R M) = 0 :=
  (eq_bot_iff_generator_eq_zero ⊥).mp rfl
/-
**Submodule.IsPrincipal.fg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.IsPrincipal`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : AddCommMonoid M] [inst_1 : Semiring R]
 [inst_2 : _root_.Module R M]   {S : Submodule R M}, S.IsPrincipal → S.FG
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Submodule.IsPrincipal.span_singleton_generator`：span_singleton_generator
 (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma fg {S : Submodule R M} (h : S.IsPrincipal) : S.FG :=
  ⟨{h.generator}, by simp only [Finset.coe_singleton, span_singleton_generator]⟩

-- See note [lower instance priority]
/-
**Submodule.IsPrincipal.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.IsPrincipal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) _root_.PrincipalIdealRing.isNoetherianRing [IsPrincipalIdealRing R] :
    IsNoetherianRing R where
  noetherian S := (IsPrincipalIdealRing.principal S).fg

-- See note [lower instance priority]
/-
**Submodule.IsPrincipal.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.IsPrincipal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) _root_.IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
    [IsNoetherianRing R] [IsBezout R] : IsPrincipalIdealRing R where
  principal S := IsBezout.isPrincipal_of_FG S (IsNoetherian.noetherian S)

end Semiring

section CommSemiring

variable [CommSemiring R] [Module R M]

/-
**Submodule.IsPrincipal.associated_generator_span_self** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule.IsPrincipal`。
形式化陈述：associated_generator_span_self [IsDomain R] (r : R) : Associated (generato
r <| Ideal.span {r}) r
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsPrincipalSpanSingletonSet`：∀ {R : Type u_1} [inst : Semiring R] {x
 : R}, Submodule.IsPrincipal (Ideal.span {x})
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `Ideal.span_singleton_generator`：∀ {R : Type u} [inst : Semiring R] (I : 
Ideal R) [inst_1 : Submodule.IsPrincipal I],   Ideal.span {Submodule.IsPrincipal
.generator I} = I
-/
theorem associated_generator_span_self [IsDomain R] (r : R) :
    Associated (generator <| Ideal.span {r}) r := by
  rw [← Ideal.span_singleton_eq_span_singleton]
  exact Ideal.span_singleton_generator _
/-
**Submodule.IsPrincipal.mem_iff_generator_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le.IsPrincipal`。
形式化陈述：mem_iff_generator_dvd (S : Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ gen
erator S ∣ x
参数：S : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.IsPrincipal.mem_iff_eq_smul_generator`：mem_iff_eq_smul_generat
or (S : Submodule R M) [S.IsPrincipal] {x : M} : x in S ↔ exists s : R, x = s • 
generator S
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iff_generator_dvd (S : Ideal R) [S.IsPrincipal] {x : R} : x ∈ S ↔ generator S ∣ x :=
  (mem_iff_eq_smul_generator S).trans (exists_congr fun a => by simp only [mul_comm, smul_eq_mul])
/-
**Submodule.IsPrincipal.prime_generator_of_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmodule.IsPrincipal`。
形式化陈述：prime_generator_of_isPrime (S : Ideal R) [S.IsPrincipal] [is_prime : S.IsP
rime] (ne_bot : S != ⊥) : Prime (generator S)
参数：S : Ideal R；ne_bot : S != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero`：eq_bot_iff_generator
_eq_zero (S : Submodule R M) [S.IsPrincipal] : S = ⊥ ↔ generator S = 0
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `Submodule.IsPrincipal.generator_mem`：generator_mem (S : Submodule R M) [
S.IsPrincipal] : generator S in S
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsPrincipal.mem_iff_generator_dvd`：mem_iff_generator_dvd (S : 
Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ generator S ∣ x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsPrime.mem_or_mem'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal
 α} [self : I.IsPrime] {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
-/
theorem prime_generator_of_isPrime (S : Ideal R) [S.IsPrincipal] [is_prime : S.IsPrime]
    (ne_bot : S ≠ ⊥) : Prime (generator S) :=
  ⟨fun h => ne_bot ((eq_bot_iff_generator_eq_zero S).2 h), fun h =>
    is_prime.ne_top (S.eq_top_of_isUnit_mem (generator_mem S) h), fun _ _ => by
    simpa only [← mem_iff_generator_dvd S] using is_prime.2⟩

-- Note that the converse may not hold if `ϕ` is not injective.
/-
**Submodule.IsPrincipal.generator_map_dvd_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule.IsPrincipal`。
形式化陈述：generator_map_dvd_of_mem {N : Submodule R M} (ϕ : M ->ₗ[R] R) [(N.map ϕ).I
sPrincipal] {x : M} (hx : x in N) : generator (N.map ϕ) ∣ ϕ x
参数：ϕ : M ->ₗ[R] R；N.map ϕ；hx : x in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsPrincipal.mem_iff_generator_dvd`：mem_iff_generator_dvd (S : 
Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ generator S ∣ x
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
-/
theorem generator_map_dvd_of_mem {N : Submodule R M} (ϕ : M →ₗ[R] R) [(N.map ϕ).IsPrincipal] {x : M}
    (hx : x ∈ N) : generator (N.map ϕ) ∣ ϕ x := by
  rw [← mem_iff_generator_dvd, Submodule.mem_map]
  exact ⟨x, hx, rfl⟩

-- Note that the converse may not hold if `ϕ` is not injective.
/-
**Submodule.IsPrincipal.generator_submoduleImage_dvd_of_mem** 是 Mathlib 中的一个定理，位
于命名空间 `Submodule.IsPrincipal`。
形式化陈述：generator_submoduleImage_dvd_of_mem {N O : Submodule R M} (hNO : N <= O) (
ϕ : O ->ₗ[R] R) [(ϕ.submoduleImage N).IsPrincipal] {x : M} (hx : x in N) : gener
ator (ϕ.submoduleImage N) ∣ ϕ ⟨x, hNO hx⟩
参数：hNO : N <= O；ϕ : O ->ₗ[R] R；ϕ.submoduleImage N；hx : x in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsPrincipal.mem_iff_generator_dvd`：mem_iff_generator_dvd (S : 
Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ generator S ∣ x
· 使用定理 `LinearMap.mem_submoduleImage_of_le`：mem_submoduleImage_of_le {M' : Type*
} [AddCommMonoid M'] [Module R M'] {O : Submodule R M} {ϕ : O ->ₗ[R] M'} {N : Su
bmodule R M} (hNO : N <=…
-/
theorem generator_submoduleImage_dvd_of_mem {N O : Submodule R M} (hNO : N ≤ O) (ϕ : O →ₗ[R] R)
    [(ϕ.submoduleImage N).IsPrincipal] {x : M} (hx : x ∈ N) :
    generator (ϕ.submoduleImage N) ∣ ϕ ⟨x, hNO hx⟩ := by
  rw [← mem_iff_generator_dvd, LinearMap.mem_submoduleImage_of_le hNO]
  exact ⟨x, hx, rfl⟩
/-
**Submodule.IsPrincipal.dvd_generator_span_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule.IsPrincipal`。
形式化陈述：dvd_generator_span_iff {r : R} {s : Set R} [(Ideal.span s).IsPrincipal] : 
r ∣ generator (Ideal.span s) ↔ forall x in s, r ∣ x where mp h x hx
参数：Ideal.span s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.IsPrincipal.mem_iff_generator_dvd`：mem_iff_generator_dvd (S : 
Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ generator S ∣ x
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
· 使用定理 `Submodule.IsPrincipal.generator_mem`：generator_mem (S : Submodule R M) [
S.IsPrincipal] : generator S in S
-/
theorem dvd_generator_span_iff {r : R} {s : Set R} [(Ideal.span s).IsPrincipal] :
    r ∣ generator (Ideal.span s) ↔ ∀ x ∈ s, r ∣ x where
  mp h x hx := h.trans <| (mem_iff_generator_dvd _).mp (Ideal.subset_span hx)
  mpr h := have : (span R s).IsPrincipal := ‹_›
    span_induction h (dvd_zero _) (fun _ _ _ _ ↦ dvd_add) (fun _ _ _ ↦ (·.mul_left _))
      (generator_mem _)

end CommSemiring

end Submodule.IsPrincipal

namespace IsBezout

section

variable [Ring R]

/-
**IsBezout.span_pair_isPrincipal** 是 Mathlib 中的一个实例，位于命名空间 `IsBezout`。
形式化陈述：span_pair_isPrincipal [IsBezout R] (x y : R) : (Ideal.span {x, y}).IsPrinc
ipal
参数：x y : R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBezout.isPrincipal_of_FG`：∀ {R : Type u} {inst : Semiring R} [self : I
sBezout R] (I : Ideal R), I.FG → Submodule.IsPrincipal I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance span_pair_isPrincipal [IsBezout R] (x y : R) : (Ideal.span {x, y}).IsPrincipal := by
  classical exact isPrincipal_of_FG (Ideal.span {x, y}) ⟨{x, y}, by simp⟩

variable (x y : R) [(Ideal.span {x, y}).IsPrincipal]

/-- A choice of gcd of two elements in a Bézout domain.

Note that the choice is usually not unique. -/
/-
**IsBezout.gcd** 是 Mathlib 中的一个定义，位于命名空间 `IsBezout`。
形式化陈述：gcd : R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of gcd of two elements in a Bézout domain.

Note that the choice is usually not unique.
-/
noncomputable def gcd : R := Submodule.IsPrincipal.generator (Ideal.span {x, y})
/-
**IsBezout.span_gcd** 是 Mathlib 中的一个定理，位于命名空间 `IsBezout`。
形式化陈述：span_gcd : Ideal.span {gcd x y} = Ideal.span {x, y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.span_singleton_generator`：∀ {R : Type u} [inst : Semiring R] (I : 
Ideal R) [inst_1 : Submodule.IsPrincipal I],   Ideal.span {Submodule.IsPrincipal
.generator I} = I
-/
theorem span_gcd : Ideal.span {gcd x y} = Ideal.span {x, y} :=
  Ideal.span_singleton_generator _

end

variable [CommRing R] (x y z : R) [(Ideal.span {x, y}).IsPrincipal]

/-
**IsBezout.gcd_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 `IsBezout`。
形式化陈述：gcd_dvd_left : gcd x y ∣ x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.IsPrincipal.mem_iff_generator_dvd`：mem_iff_generator_dvd (S : 
Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ generator S ∣ x
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem gcd_dvd_left : gcd x y ∣ x :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))
/-
**IsBezout.gcd_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 `IsBezout`。
形式化陈述：gcd_dvd_right : gcd x y ∣ y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.IsPrincipal.mem_iff_generator_dvd`：mem_iff_generator_dvd (S : 
Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ generator S ∣ x
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem gcd_dvd_right : gcd x y ∣ y :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))

variable {x y z} in
/-
**IsBezout.dvd_gcd** 是 Mathlib 中的一个定理，位于命名空间 `IsBezout`。
形式化陈述：dvd_gcd (hx : z ∣ x) (hy : z ∣ y) : z ∣ gcd x y
参数：hx : z ∣ x；hy : z ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_le_span_singleton`：span_singleton_le_span_singleton
 {x y : α} : span ({x} : Set α) <= span ({y} : Set α) ↔ y ∣ x
· 使用定理 `IsBezout.span_gcd`：span_gcd : Ideal.span {gcd x y} = Ideal.span {x, y}
· 使用定理 `Ideal.span_insert`：span_insert (x) (s : Set α) : span (insert x s) = spa
n ({x} : Set α) ⊔ span s
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
-/
theorem dvd_gcd (hx : z ∣ x) (hy : z ∣ y) : z ∣ gcd x y := by
  rw [← Ideal.span_singleton_le_span_singleton] at hx hy ⊢
  rw [span_gcd, Ideal.span_insert, sup_le_iff]
  exact ⟨hx, hy⟩
/-
**IsBezout.gcd_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `IsBezout`。
形式化陈述：gcd_eq_sum : exists a b : R, a * x + b * y = gcd x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_span_pair`：mem_span_pair {x y z : α} : z in span ({x, y} : Set
 α) ↔ exists a b, a * x + b * y = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsBezout.span_gcd`：span_gcd : Ideal.span {gcd x y} = Ideal.span {x, y}
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gcd_eq_sum : ∃ a b : R, a * x + b * y = gcd x y :=
  Ideal.mem_span_pair.mp (by rw [← span_gcd]; apply Ideal.subset_span; simp)

variable {x y}
/-
**IsBezout._root_.IsRelPrime.isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `IsBezout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsRelPrime.isCoprime (h : IsRelPrime x y) : IsCoprime x y := by
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq, ← Ideal.span_union,
    Set.singleton_union, ← span_gcd, Ideal.span_singleton_eq_top]
  exact h (gcd_dvd_left x y) (gcd_dvd_right x y)
/-
**IsBezout._root_.isRelPrime_iff_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `IsBezout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isRelPrime_iff_isCoprime : IsRelPrime x y ↔ IsCoprime x y :=
  ⟨IsRelPrime.isCoprime, IsCoprime.isRelPrime⟩

variable (R)

/-- Any Bézout domain is a GCD domain. This is not an instance since `GCDMonoid` contains data,
and this might not be how we would like to construct it. -/
@[instance_reducible]
/-
**IsBezout.toGCDDomain** 是 Mathlib 中的一个定义，位于命名空间 `IsBezout`。
形式化陈述：toGCDDomain [IsBezout R] [IsCancelMulZero R] [DecidableEq R] : GCDMonoid R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any Bézout domain is a GCD domain. This is not an instance since `GCDMonoid` con
tains data,
and this might not be how we would like to construct it.
-/
noncomputable def toGCDDomain [IsBezout R] [IsCancelMulZero R] [DecidableEq R] : GCDMonoid R :=
  gcdMonoidOfGCD (gcd · ·) (gcd_dvd_left · ·) (gcd_dvd_right · ·) dvd_gcd
/-
**IsBezout.** 是 Mathlib 中的一个实例，位于命名空间 `IsBezout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsBezout R] [IsCancelMulZero R] : IsGCDMonoid R := by
  classical exact ⟨toGCDDomain R⟩
/-
**IsBezout.associated_gcd_gcd** 是 Mathlib 中的一个定理，位于命名空间 `IsBezout`。
形式化陈述：associated_gcd_gcd [GCDMonoid R] : Associated (IsBezout.gcd x y) (GCDMonoi
d.gcd x y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `gcd_greatest_associated`：gcd_greatest_associated {α : Type*} [CommMonoid
WithZero α] [GCDMonoid α] {a b d : α} (hda : d ∣ a) (hdb : d ∣ b) (hd : forall e
 : α, e ∣ a -…
· 使用定理 `IsBezout.gcd_dvd_left`：gcd_dvd_left : gcd x y ∣ x
· 使用定理 `IsBezout.gcd_dvd_right`：gcd_dvd_right : gcd x y ∣ y
· 使用定理 `IsBezout.dvd_gcd`：dvd_gcd (hx : z ∣ x) (hy : z ∣ y) : z ∣ gcd x y
-/
theorem associated_gcd_gcd [GCDMonoid R] : Associated (IsBezout.gcd x y) (GCDMonoid.gcd x y) :=
  gcd_greatest_associated (gcd_dvd_left _ _) (gcd_dvd_right _ _) (fun _ => dvd_gcd)

end IsBezout

/-- A version of Bézout's lemma for greatest common divisors over arbitrary `Finset`s. -/
/-
**Finset.gcd_eq_sum_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.gcd_eq_sum_mul {α : Type*} [CommRing R] [IsBezout R] [NormalizedGCD
Monoid R] (s : Finset α) (f : α -> R) : exists g : α -> R, s.gcd f = ∑ a in s, f
 a * g a
参数：s : Finset α；f : α -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `IsBezout.gcd_eq_sum`：gcd_eq_sum : exists a b : R, a * x + b * y = gcd x 
y
· 使用定理 `IsBezout.associated_gcd_gcd`：associated_gcd_gcd [GCDMonoid R] : Associat
ed (IsBezout.gcd x y) (GCDMonoid.gcd x y)
· 使用定理 `Finset.gcd_insert`：gcd_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f)
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a

--- 原说明 ---
A version of Bézout's lemma for greatest common divisors over arbitrary `Finset`
s.
-/
lemma Finset.gcd_eq_sum_mul {α : Type*} [CommRing R] [IsBezout R] [NormalizedGCDMonoid R]
    (s : Finset α) (f : α → R) :
    ∃ g : α → R, s.gcd f = ∑ a ∈ s, f a * g a := by classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨x, y, hxy⟩ := IsBezout.gcd_eq_sum (f a) (s.gcd f)
    obtain ⟨u, hu⟩ := IsBezout.associated_gcd_gcd R (x := f a) (y := s.gcd f)
    rw [← hxy, add_mul, mul_comm x, mul_comm y] at hu
    obtain ⟨g, hg⟩ := ih
    refine ⟨Function.update (g · * (y * u)) a (x * u), ?_⟩
    rw [gcd_insert, sum_insert ha, ← hu, hg]
    simp only [Function.update_self, add_right_inj, sum_mul, mul_assoc]
    exact sum_congr rfl fun b hb ↦ congrArg (f b * ·) <|
      (Function.update_of_ne (show b ≠ a by grind) (x * u) (g · * (y * u))).symm

namespace IsPrime

open Submodule.IsPrincipal Ideal

-- TODO -- for a non-ID one could perhaps prove that if p < q are prime then q maximal;
-- 0 isn't prime in a non-ID PIR but the Krull dimension is still <= 1.
-- The below result follows from this, but we could also use the below result to
-- prove this (quotient out by p).
/-
**IsPrime.to_maximal_ideal** 是 Mathlib 中的一个定理，位于命名空间 `IsPrime`。
形式化陈述：to_maximal_ideal [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {S : I
deal R} [hpi : IsPrime S] (hS : S != ⊥) : IsMaximal S
参数：hS : S != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isMaximal_iff`：isMaximal_iff {I : Ideal α} : I.IsMaximal ↔ (1 : α)
 ∉ I ∧ forall (J : Ideal α) (x), I <= J -> x ∉ I -> x in J -> (1 : α) in J
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `Submodule.IsPrincipal.mem_iff_generator_dvd`：mem_iff_generator_dvd (S : 
Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ generator S ∣ x
· 使用定理 `Submodule.IsPrincipal.generator_mem`：generator_mem (S : Submodule R M) [
S.IsPrincipal] : generator S in S
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_generator`：∀ {R : Type u} [inst : Semiring R] (I : 
Ideal R) [inst_1 : Submodule.IsPrincipal I],   Ideal.span {Submodule.IsPrincipal
.generator I} = I
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero`：eq_bot_iff_generator
_eq_zero (S : Submodule R M) [S.IsPrincipal] : S = ⊥ ↔ generator S = 0
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem to_maximal_ideal [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {S : Ideal R}
    [hpi : IsPrime S] (hS : S ≠ ⊥) : IsMaximal S :=
  isMaximal_iff.2
    ⟨(ne_top_iff_one S).1 hpi.1, by
      intro T x hST hxS hxT
      obtain ⟨z, hz⟩ := (mem_iff_generator_dvd _).1 (hST <| generator_mem S)
      cases hpi.mem_or_mem (show generator T * z ∈ S from hz ▸ generator_mem S) with
      | inl h =>
        have hTS : T ≤ S := by
          rwa [← T.span_singleton_generator, Ideal.span_le, singleton_subset_iff]
        exact (hxS <| hTS hxT).elim
      | inr h =>
        obtain ⟨y, hy⟩ := (mem_iff_generator_dvd _).1 h
        have : generator S ≠ 0 := mt (eq_bot_iff_generator_eq_zero _).2 hS
        rw [← mul_one (generator S), hy, mul_left_comm, mul_right_inj' this] at hz
        exact hz.symm ▸ T.mul_mem_right _ (generator_mem T)⟩

end IsPrime

section

open EuclideanDomain

variable [EuclideanDomain R]

/-
**mod_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mod_mem_iff {S : Ideal R} {x y : R} (hy : y in S) : x % y in S ↔ x in S
参数：hy : y in S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `EuclideanDomain.div_add_mod`：div_add_mod (a b : R) : b * (a / b) + a % b
 = a
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanDomain.mod_eq_sub_mul_div`：mod_eq_sub_mul_div {R : Type*} [Eucl
ideanDomain R] (a b : R) : a % b = a - b * (a / b)
-/
theorem mod_mem_iff {S : Ideal R} {x y : R} (hy : y ∈ S) : x % y ∈ S ↔ x ∈ S :=
  ⟨fun hxy => div_add_mod x y ▸ S.add_mem (S.mul_mem_right _ hy) hxy, fun hx =>
    (mod_eq_sub_mul_div x y).symm ▸ S.sub_mem hx (S.mul_mem_right _ hy)⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) EuclideanDomain.to_principal_ideal_domain : IsPrincipalIdealRing R where
  principal S := by classical exact
    ⟨if h : { x : R | x ∈ S ∧ x ≠ 0 }.Nonempty then
        have wf : WellFounded (EuclideanDomain.r : R → R → Prop) := EuclideanDomain.r_wellFounded
        have hmin : WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ∈ S ∧
            WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ≠ 0 :=
          WellFounded.min_mem wf { x : R | x ∈ S ∧ x ≠ 0 } h
        ⟨WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h,
          Submodule.ext fun x => ⟨fun hx =>
            div_add_mod x (WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h) ▸
              (Ideal.mem_span_singleton.2 <| dvd_add (dvd_mul_right _ _) <| by
                have : x % WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ∉
                    { x : R | x ∈ S ∧ x ≠ 0 } :=
                  fun h₁ => WellFounded.not_lt_min wf _ h₁ (mod_lt x hmin.2)
                have : x % WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h = 0 := by
                  simp only [not_and_or, Set.mem_ofPred_eq, not_ne_iff] at this
                  exact this.neg_resolve_left <| (mod_mem_iff hmin.1).2 hx
                simp [*]),
              fun hx =>
                let ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
                hy.symm ▸ S.mul_mem_right _ hmin.1⟩⟩
      else ⟨0, Submodule.ext fun a => by
            rw [← @Submodule.bot_coe R R _ _ _, span_eq, Submodule.mem_bot]
            exact ⟨fun haS => by_contra fun ha0 => h ⟨a, ⟨haS, ha0⟩⟩,
              fun h₁ => h₁.symm ▸ S.zero_mem⟩⟩⟩

end

/-
**IsField.isPrincipalIdealRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsField.isPrincipalIdealRing {R : Type*} [Ring R] (h : IsField R) : IsPrin
cipalIdealRing R
参数：h : IsField R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
-/
theorem IsField.isPrincipalIdealRing {R : Type*} [Ring R] (h : IsField R) :
    IsPrincipalIdealRing R :=
  @EuclideanDomain.to_principal_ideal_domain R (@Field.toEuclideanDomain R h.toField)

namespace PrincipalIdealRing

open IsPrincipalIdealRing

/-
**PrincipalIdealRing.isMaximal_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Princip
alIdealRing`。
形式化陈述：isMaximal_of_irreducible [CommSemiring R] [IsPrincipalIdealRing R] {p : R}
 (hp : Irreducible p) : Ideal.IsMaximal (span R ({p} : Set R))
参数：hp : Irreducible p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_eq_top`：span_singleton_eq_top {x} : span ({x} : Set
 α) = ⊤ ↔ IsUnit x
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Ideal.span_singleton_le_span_singleton`：span_singleton_le_span_singleton
 {x y : α} : span ({x} : Set α) <= span ({y} : Set α) ↔ y ∣ x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `of_irreducible_mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Irredu
cible (a * b) → IsUnit a ∨ IsUnit b
· 使用定理 `IsUnit.mul_right_dvd`：mul_right_dvd (hu : IsUnit u) : a * u ∣ b ↔ a ∣ b
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isMaximal_of_irreducible [CommSemiring R] [IsPrincipalIdealRing R] {p : R}
    (hp : Irreducible p) : Ideal.IsMaximal (span R ({p} : Set R)) :=
  ⟨⟨mt Ideal.span_singleton_eq_top.1 hp.1, fun I hI => by
      rcases principal I with ⟨a, rfl⟩
      rw [Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
      rcases Ideal.span_singleton_le_span_singleton.1 (le_of_lt hI) with ⟨b, rfl⟩
      refine (of_irreducible_mul hp).resolve_right (mt (fun hb => ?_) (not_le_of_gt hI))
      rw [Ideal.submodule_span_eq, Ideal.submodule_span_eq,
        Ideal.span_singleton_le_span_singleton, IsUnit.mul_right_dvd hb]⟩⟩
/-
**PrincipalIdealRing._root_.Ideal.irreducible_iff_isMaximal_span_singleton** 是 M
athlib 中的一个定理，位于命名空间 `PrincipalIdealRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ideal.irreducible_iff_isMaximal_span_singleton
    [CommSemiring R] [IsPrincipalIdealRing R] [IsDomain R] {p : R} (hp : p ≠ 0) :
    Irreducible p ↔ Ideal.IsMaximal (span R ({p} : Set R)) :=
  ⟨isMaximal_of_irreducible, Ideal.irreducible_of_isMaximal_span_singleton hp⟩

variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

section

open scoped Classical in
/-- `factors a` is a multiset of irreducible elements whose product is `a`, up to units -/
/-
**PrincipalIdealRing.factors** 是 Mathlib 中的一个定义，位于命名空间 `PrincipalIdealRing`。
形式化陈述：factors (a : R) : Multiset R
参数：a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`factors a` is a multiset of irreducible elements whose product is `a`, up to un
its
-/
noncomputable def factors (a : R) : Multiset R :=
  if h : a = 0 then ∅ else Classical.choose (WfDvdMonoid.exists_factors a h)
/-
**PrincipalIdealRing.factors_spec** 是 Mathlib 中的一个定理，位于命名空间 `PrincipalIdealRing`
。
形式化陈述：factors_spec (a : R) (h : a != 0) : (forall b in factors a, Irreducible b)
 ∧ Associated (factors a).prod a
参数：a : R；h : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `WfDvdMonoid.exists_factors`：exists_factors (a : α) : a != 0 -> exists f 
: Multiset α, (forall b in f, Irreducible b) ∧ Associated f.prod a
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `ufm_of_decomposition_of_wfDvdMonoid`：∀ {α : Type u_1} [inst : CommMonoid
WithZero α] [IsCancelMulZero α] [WfDvdMonoid α] [DecompositionMonoid α],   Uniqu
eFactorizationMonoid α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsNoetherianRing.wfDvdMonoid`：∀ {R : Type u_1} [inst : CommSemiring R] [
IsDomain R] [h : IsNoetherianRing R], WfDvdMonoid R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `IsBezout.instIsGCDMonoidOfIsCancelMulZero`：∀ (R : Type u) [inst : CommRi
ng R] [IsBezout R] [IsCancelMulZero R], IsGCDMonoid R
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
-/
theorem factors_spec (a : R) (h : a ≠ 0) :
    (∀ b ∈ factors a, Irreducible b) ∧ Associated (factors a).prod a := by
  unfold factors; rw [dif_neg h]
  exact Classical.choose_spec (WfDvdMonoid.exists_factors a h)
/-
**PrincipalIdealRing.ne_zero_of_mem_factors** 是 Mathlib 中的一个定理，位于命名空间 `Principal
IdealRing`。
形式化陈述：ne_zero_of_mem_factors {R : Type v} [CommRing R] [IsDomain R] [IsPrincipal
IdealRing R] {a b : R} (ha : a != 0) (hb : b in factors a) : b != 0
参数：ha : a != 0；hb : b in factors a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PrincipalIdealRing.factors_spec`：factors_spec (a : R) (h : a != 0) : (fo
rall b in factors a, Irreducible b) ∧ Associated (factors a).prod a
-/
theorem ne_zero_of_mem_factors {R : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {a b : R} (ha : a ≠ 0) (hb : b ∈ factors a) : b ≠ 0 :=
  Irreducible.ne_zero ((factors_spec a ha).1 b hb)
/-
**PrincipalIdealRing.mem_submonoid_of_factors_subset_of_units_subset** 是 Mathlib
 中的一个定理，位于命名空间 `PrincipalIdealRing`。
形式化陈述：mem_submonoid_of_factors_subset_of_units_subset (s : Submonoid R) {a : R} 
(ha : a != 0) (hfac : forall b in factors a, b in s) (hunit : forall c : Rˣ, (c 
: R) in s) : a in s
参数：s : Submonoid R；ha : a != 0；hfac : forall b in factors a, b in s；hunit : fora
ll c : Rˣ, (c : R) in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PrincipalIdealRing.factors_spec`：factors_spec (a : R) (h : a != 0) : (fo
rall b in factors a, Irreducible b) ∧ Associated (factors a).prod a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
-/
theorem mem_submonoid_of_factors_subset_of_units_subset (s : Submonoid R) {a : R} (ha : a ≠ 0)
    (hfac : ∀ b ∈ factors a, b ∈ s) (hunit : ∀ c : Rˣ, (c : R) ∈ s) : a ∈ s := by
  rcases (factors_spec a ha).2 with ⟨c, hc⟩
  rw [← hc]
  exact mul_mem (multiset_prod_mem _ hfac) (hunit _)

/-- If a `RingHom` maps all units and all factors of an element `a` into a submonoid `s`, then it
also maps `a` into that submonoid. -/
/-
**PrincipalIdealRing.ringHom_mem_submonoid_of_factors_subset_of_units_subset** 是
 Mathlib 中的一个定理，位于命名空间 `PrincipalIdealRing`。
形式化陈述：ringHom_mem_submonoid_of_factors_subset_of_units_subset {R S : Type*} [Com
mRing R] [IsDomain R] [IsPrincipalIdealRing R] [NonAssocSemiring S] (f : R ->+* 
S) (s : Submonoid S) (a : R) (ha : a != 0) (h : forall b in factors a, f b in s)
 (hf : forall c : Rˣ, f c in s) : f a in s
参数：f : R ->+* S；s : Submonoid S；a : R；ha : a != 0；h : forall b in factors a, f b
 in s；hf : forall c : Rˣ, f c in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.mem_submonoid_of_factors_subset_of_units_subset`：mem_
submonoid_of_factors_subset_of_units_subset (s : Submonoid R) {a : R} (ha : a !=
 0) (hfac : forall b in factors a, b in s) (hunit : fora…

--- 原说明 ---
If a `RingHom` maps all units and all factors of an element `a` into a submonoid
 `s`, then it
also maps `a` into that submonoid.
-/
theorem ringHom_mem_submonoid_of_factors_subset_of_units_subset {R S : Type*} [CommRing R]
    [IsDomain R] [IsPrincipalIdealRing R] [NonAssocSemiring S] (f : R →+* S) (s : Submonoid S)
    (a : R) (ha : a ≠ 0) (h : ∀ b ∈ factors a, f b ∈ s) (hf : ∀ c : Rˣ, f c ∈ s) : f a ∈ s :=
  mem_submonoid_of_factors_subset_of_units_subset (s.comap f.toMonoidHom) ha h hf

-- see Note [lower instance priority]
/-- A principal ideal domain has unique factorization -/
/-
**PrincipalIdealRing.** 是 Mathlib 中的一个实例，位于命名空间 `PrincipalIdealRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A principal ideal domain has unique factorization
-/
instance (priority := 100) to_uniqueFactorizationMonoid : UniqueFactorizationMonoid R :=
  { (IsNoetherianRing.wfDvdMonoid : WfDvdMonoid R) with
    irreducible_iff_prime := irreducible_iff_prime }

end

end PrincipalIdealRing

section Surjective

open Submodule

variable {S N F : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Semiring S]
variable [Module R M] [Module R N] [FunLike F R S] [RingHomClass F R S]

/-
**Submodule.IsPrincipal.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.IsPrincipal.map (f : M ->ₗ[R] N) {S : Submodule R M} (hI : IsPri
ncipal S) : IsPrincipal (map f S)
参数：f : M ->ₗ[R] N；hI : IsPrincipal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.IsPrincipal.span_singleton_generator`：span_singleton_generator
 (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S
-/
theorem Submodule.IsPrincipal.map (f : M →ₗ[R] N) {S : Submodule R M}
    (hI : IsPrincipal S) : IsPrincipal (map f S) :=
  ⟨⟨f (IsPrincipal.generator S), by
      rw [← Set.image_singleton, ← map_span, span_singleton_generator]⟩⟩
/-
**Submodule.IsPrincipal.of_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.IsPrincipal.of_comap (f : M ->ₗ[R] N) (hf : Function.Surjective 
f) (S : Submodule R N) [hI : IsPrincipal (S.comap f)] : IsPrincipal S
参数：f : M ->ₗ[R] N；hf : Function.Surjective f；S : Submodule R N；S.comap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_comap_eq_of_surjective`：map_comap_eq_of_surjective (p : Su
bmodule R₂ M₂) : (p.comap f).map f = p
· 使用定理 `Submodule.IsPrincipal.map`：Submodule.IsPrincipal.map (f : M ->ₗ[R] N) {S
 : Submodule R M} (hI : IsPrincipal S) : IsPrincipal (map f S)
-/
theorem Submodule.IsPrincipal.of_comap (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (S : Submodule R N) [hI : IsPrincipal (S.comap f)] : IsPrincipal S := by
  rw [← Submodule.map_comap_eq_of_surjective hf S]
  exact hI.map f
/-
**Submodule.IsPrincipal.map_ringHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.IsPrincipal.map_ringHom (f : F) {I : Ideal R} (hI : IsPrincipal 
I) : IsPrincipal (Ideal.map f I)
参数：f : F；hI : IsPrincipal I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Ideal.span_singleton_generator`：∀ {R : Type u} [inst : Semiring R] (I : 
Ideal R) [inst_1 : Submodule.IsPrincipal I],   Ideal.span {Submodule.IsPrincipal
.generator I} = I
-/
theorem Submodule.IsPrincipal.map_ringHom (f : F) {I : Ideal R}
    (hI : IsPrincipal I) : IsPrincipal (Ideal.map f I) :=
  ⟨⟨f (IsPrincipal.generator I), by
      rw [Ideal.submodule_span_eq, ← Set.image_singleton, ← Ideal.map_span,
      Ideal.span_singleton_generator]⟩⟩
/-
**Ideal.IsPrincipal.of_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsPrincipal.of_comap (f : F) (hf : Function.Surjective f) (I : Ideal
 S) [hI : IsPrincipal (I.comap f)] : IsPrincipal I
参数：f : F；hf : Function.Surjective f；I : Ideal S；I.comap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
· 使用定理 `Submodule.IsPrincipal.map_ringHom`：Submodule.IsPrincipal.map_ringHom (f 
: F) {I : Ideal R} (hI : IsPrincipal I) : IsPrincipal (Ideal.map f I)
-/
theorem Ideal.IsPrincipal.of_comap (f : F) (hf : Function.Surjective f) (I : Ideal S)
    [hI : IsPrincipal (I.comap f)] : IsPrincipal I := by
  rw [← map_comap_of_surjective f hf I]
  exact hI.map_ringHom f

/-- The surjective image of a principal ideal ring is again a principal ideal ring. -/
/-
**IsPrincipalIdealRing.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrincipalIdealRing.of_surjective [IsPrincipalIdealRing R] (f : F) (hf : 
Function.Surjective f) : IsPrincipalIdealRing S
参数：f : F；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrincipal.of_comap`：Ideal.IsPrincipal.of_comap (f : F) (hf : Fun
ction.Surjective f) (I : Ideal S) [hI : IsPrincipal (I.comap f)] : IsPrincipal I
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S

--- 原说明 ---
The surjective image of a principal ideal ring is again a principal ideal ring.
-/
theorem IsPrincipalIdealRing.of_surjective [IsPrincipalIdealRing R] (f : F)
    (hf : Function.Surjective f) : IsPrincipalIdealRing S :=
  ⟨fun I => Ideal.IsPrincipal.of_comap f hf I⟩
/-
**isPrincipalIdealRing_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrincipalIdealRing_prod_iff : IsPrincipalIdealRing (R × S) ↔ IsPrincipal
IdealRing R ∧ IsPrincipalIdealRing S where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.of_surjective`：IsPrincipalIdealRing.of_surjective [
IsPrincipalIdealRing R] (f : F) (hf : Function.Surjective f) : IsPrincipalIdealR
ing S
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
· 使用定理 `instIsPrincipalIdealRingProd`：∀ {R : Type u} {S : Type v} [inst : Semiri
ng R] [inst_1 : Semiring S] [IsPrincipalIdealRing R] [IsPrincipalIdealRing S],  
 IsPrincipalIdealR…
-/
theorem isPrincipalIdealRing_prod_iff :
    IsPrincipalIdealRing (R × S) ↔ IsPrincipalIdealRing R ∧ IsPrincipalIdealRing S where
  mp h := ⟨h.of_surjective (RingHom.fst R S) Prod.fst_surjective,
    h.of_surjective (RingHom.snd R S) Prod.snd_surjective⟩
  mpr := fun ⟨_, _⟩ ↦ inferInstance
/-
**isPrincipalIdealRing_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrincipalIdealRing_pi_iff {ι} [Finite ι] {R : ι -> Type*} [forall i, Sem
iring (R i)] : IsPrincipalIdealRing (Π i, R i) ↔ forall i, IsPrincipalIdealRing 
(R i) where mp h i
参数：R i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.of_surjective`：IsPrincipalIdealRing.of_surjective [
IsPrincipalIdealRing R] (f : F) (hf : Function.Surjective f) : IsPrincipalIdealR
ing S
· 使用定理 `Function.surjective_eval`：surjective_eval {α : Sort u} {β : α -> Sort v}
 [h : forall a, Nonempty (β a)] (a : α) : Surjective (eval a : (forall a, β a) -
> β a)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Ideal.instIsPrincipalIdealRingForallOfFinite`：∀ {ι : Type u_4} {R : ι → 
Type u_5} [inst : (i : ι) → Semiring (R i)] [Finite ι]   [∀ (i : ι), IsPrincipal
IdealRing (R i)], IsPrincipalIdeal…
-/
theorem isPrincipalIdealRing_pi_iff {ι} [Finite ι] {R : ι → Type*} [∀ i, Semiring (R i)] :
    IsPrincipalIdealRing (Π i, R i) ↔ ∀ i, IsPrincipalIdealRing (R i) where
  mp h i := h.of_surjective (Pi.evalRingHom R i) (Function.surjective_eval _)
  mpr _ := inferInstance

end Surjective

section

open Ideal

variable [CommRing R]

section Bezout
variable [IsBezout R]

/-
**isCoprime_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_of_dvd (x y : R) (nonzero : ¬(x = 0 ∧ y = 0)) (H : forall z in n
onunits R, z != 0 -> z ∣ x -> ¬z ∣ y) : IsCoprime x y
参数：x y : R；nonzero : ¬(x = 0 ∧ y = 0)；H : forall z in nonunits R, z != 0 -> z ∣ 
x -> ¬z ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.isCoprime`：∀ {R : Type u} [inst : CommRing R] {x y : R} [Subm
odule.IsPrincipal (Ideal.span {x, y})], IsRelPrime x y → IsCoprime x y
· 使用定理 `isRelPrime_of_no_nonunits_factors`：isRelPrime_of_no_nonunits_factors [Mo
noidWithZero α] {x y : α} (nonzero : ¬(x = 0 ∧ y = 0)) (H : forall z, ¬ IsUnit z
 -> z != 0 -> z ∣ x -> …
-/
theorem isCoprime_of_dvd (x y : R) (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z ∈ nonunits R, z ≠ 0 → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  (isRelPrime_of_no_nonunits_factors nonzero H).isCoprime
/-
**dvd_or_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_or_isCoprime (x y : R) (h : Irreducible x) : x ∣ y ∨ IsCoprime x y
参数：x y : R；h : Irreducible x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `IsRelPrime.isCoprime`：∀ {R : Type u} [inst : CommRing R] {x y : R} [Subm
odule.IsPrincipal (Ideal.span {x, y})], IsRelPrime x y → IsCoprime x y
· 使用引理 `Irreducible.dvd_or_isRelPrime`：Irreducible.dvd_or_isRelPrime [Monoid M] 
{p n : M} (hp : Irreducible p) : p ∣ n ∨ IsRelPrime p n
-/
theorem dvd_or_isCoprime (x y : R) (h : Irreducible x) : x ∣ y ∨ IsCoprime x y :=
  h.dvd_or_isRelPrime.imp_right IsRelPrime.isCoprime

/-- See also `Irreducible.isRelPrime_iff_not_dvd`. -/
/-
**Irreducible.coprime_iff_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.coprime_iff_not_dvd {p n : R} (hp : Irreducible p) : IsCoprime
 p n ↔ ¬p ∣ n
参数：hp : Irreducible p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isRelPrime_iff_isCoprime`：∀ {R : Type u} [inst : CommRing R] {x y : R} [
Submodule.IsPrincipal (Ideal.span {x, y})], IsRelPrime x y ↔ IsCoprime x y
· 使用引理 `Irreducible.isRelPrime_iff_not_dvd`：Irreducible.isRelPrime_iff_not_dvd [
Monoid M] {p n : M} (hp : Irreducible p) : IsRelPrime p n ↔ ¬ p ∣ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See also `Irreducible.isRelPrime_iff_not_dvd`.
-/
theorem Irreducible.coprime_iff_not_dvd {p n : R} (hp : Irreducible p) :
    IsCoprime p n ↔ ¬p ∣ n := by rw [← isRelPrime_iff_isCoprime, hp.isRelPrime_iff_not_dvd]

/-- See also `Irreducible.coprime_iff_not_dvd'`. -/
/-
**Irreducible.dvd_iff_not_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.dvd_iff_not_isCoprime {p n : R} (hp : Irreducible p) : p ∣ n ↔
 ¬IsCoprime p n
参数：hp : Irreducible p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `Irreducible.coprime_iff_not_dvd`：Irreducible.coprime_iff_not_dvd {p n : 
R} (hp : Irreducible p) : IsCoprime p n ↔ ¬p ∣ n

--- 原说明 ---
See also `Irreducible.coprime_iff_not_dvd'`.
-/
theorem Irreducible.dvd_iff_not_isCoprime {p n : R} (hp : Irreducible p) : p ∣ n ↔ ¬IsCoprime p n :=
  iff_not_comm.2 hp.coprime_iff_not_dvd
/-
**Irreducible.coprime_pow_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.coprime_pow_of_not_dvd {p a : R} (m : Nat) (hp : Irreducible p
) (h : ¬p ∣ a) : IsCoprime a (p ^ m)
参数：m : Nat；hp : Irreducible p；h : ¬p ∣ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.pow_right`：IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime
 x (y ^ n)
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Irreducible.coprime_iff_not_dvd`：Irreducible.coprime_iff_not_dvd {p n : 
R} (hp : Irreducible p) : IsCoprime p n ↔ ¬p ∣ n
-/
theorem Irreducible.coprime_pow_of_not_dvd {p a : R} (m : ℕ) (hp : Irreducible p) (h : ¬p ∣ a) :
    IsCoprime a (p ^ m) :=
  (hp.coprime_iff_not_dvd.2 h).symm.pow_right
/-
**Irreducible.isCoprime_or_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.isCoprime_or_dvd {p : R} (hp : Irreducible p) (i : R) : IsCopr
ime p i ∨ p ∣ i
参数：hp : Irreducible p；i : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Irreducible.dvd_iff_not_isCoprime`：Irreducible.dvd_iff_not_isCoprime {p 
n : R} (hp : Irreducible p) : p ∣ n ↔ ¬IsCoprime p n
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem Irreducible.isCoprime_or_dvd {p : R} (hp : Irreducible p) (i : R) : IsCoprime p i ∨ p ∣ i :=
  (_root_.em _).imp_right hp.dvd_iff_not_isCoprime.2

variable [IsDomain R]

section GCD
variable [GCDMonoid R]

/-
**IsBezout.span_gcd_eq_span_gcd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBezout.span_gcd_eq_span_gcd (x y : R) : span {GCDMonoid.gcd x y} = span 
{IsBezout.gcd x y}
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsBezout.dvd_gcd`：dvd_gcd (hx : z ∣ x) (hy : z ∣ y) : z ∣ gcd x y
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
· 使用定理 `GCDMonoid.gcd_dvd_right`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a b : α), gcd a b ∣ b
· 使用定理 `GCDMonoid.dvd_gcd`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [self 
: GCDMonoid α] {a b c : α}, a ∣ c → a ∣ b → a ∣ gcd c b
· 使用定理 `IsBezout.gcd_dvd_left`：gcd_dvd_left : gcd x y ∣ x
· 使用定理 `IsBezout.gcd_dvd_right`：gcd_dvd_right : gcd x y ∣ y
-/
theorem IsBezout.span_gcd_eq_span_gcd (x y : R) :
    span {GCDMonoid.gcd x y} = span {IsBezout.gcd x y} := by
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd
    (IsBezout.dvd_gcd (GCDMonoid.gcd_dvd_left _ _) <| GCDMonoid.gcd_dvd_right _ _)
    (GCDMonoid.dvd_gcd (IsBezout.gcd_dvd_left _ _) <| IsBezout.gcd_dvd_right _ _)
/-
**span_gcd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：span_gcd (x y : R) : span {gcd x y} = span {x, y}
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsBezout.span_gcd`：span_gcd : Ideal.span {gcd x y} = Ideal.span {x, y}
· 使用定理 `IsBezout.span_gcd_eq_span_gcd`：IsBezout.span_gcd_eq_span_gcd (x y : R) :
 span {GCDMonoid.gcd x y} = span {IsBezout.gcd x y}
-/
theorem span_gcd (x y : R) : span {gcd x y} = span {x, y} := by
  rw [← IsBezout.span_gcd, IsBezout.span_gcd_eq_span_gcd]
/-
**gcd_dvd_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gcd_dvd_iff_exists (a b : R) {z} : gcd a b ∣ z ↔ exists x y, z = a * x + b
 * y
参数：a b : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem gcd_dvd_iff_exists (a b : R) {z} : gcd a b ∣ z ↔ ∃ x y, z = a * x + b * y := by
  simp_rw [mul_comm a, mul_comm b, @eq_comm _ z, ← Ideal.mem_span_pair, ← span_gcd,
    Ideal.mem_span_singleton]

/-- **Bézout's lemma** -/
/-
**exists_gcd_eq_mul_add_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_gcd_eq_mul_add_mul (a b : R) : exists x y, gcd a b = a * x + b * y
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gcd_dvd_iff_exists`：gcd_dvd_iff_exists (a b : R) {z} : gcd a b ∣ z ↔ exi
sts x y, z = a * x + b * y
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a

--- 原说明 ---
**Bézout's lemma**
-/
theorem exists_gcd_eq_mul_add_mul (a b : R) : ∃ x y, gcd a b = a * x + b * y := by
  rw [← gcd_dvd_iff_exists]
/-
**gcd_isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gcd_isUnit_iff (x y : R) : IsUnit (gcd x y) ↔ IsCoprime x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCoprime.eq_1`：∀ {R : Type u} [inst : CommSemiring R] (x y : R), IsCopr
ime x y = ∃ a b, a * x + b * y = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_span_pair`：mem_span_pair {x y z : α} : z in span ({x, y} : Set
 α) ↔ exists a b, a * x + b * y = z
· 使用定理 `span_gcd`：span_gcd (x y : R) : span {gcd x y} = span {x, y}
· 使用定理 `Ideal.span_singleton_eq_top`：span_singleton_eq_top {x} : span ({x} : Set
 α) = ⊤ ↔ IsUnit x
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem gcd_isUnit_iff (x y : R) : IsUnit (gcd x y) ↔ IsCoprime x y := by
  rw [IsCoprime, ← Ideal.mem_span_pair, ← span_gcd, ← span_singleton_eq_top, eq_top_iff_one]

end GCD

/-
**Prime.coprime_iff_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Prime.coprime_iff_not_dvd {p n : Nat} (pp : Prime p) : Coprime p n ↔ ¬p ∣ 
n
参数：pp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.coprime_iff_not_dvd`：Irreducible.coprime_iff_not_dvd {p n : 
R} (hp : Irreducible p) : IsCoprime p n ↔ ¬p ∣ n
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
theorem Prime.coprime_iff_not_dvd {p n : R} (hp : Prime p) : IsCoprime p n ↔ ¬p ∣ n :=
  hp.irreducible.coprime_iff_not_dvd
/-
**exists_associated_pow_of_mul_eq_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_associated_pow_of_mul_eq_pow' {a b c : R} (hab : IsCoprime a b) {k 
: Nat} (h : a * b = c ^ k) : exists d : R, Associated (d ^ k) a
参数：hab : IsCoprime a b；h : a * b = c ^ k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `exists_associated_pow_of_mul_eq_pow`：exists_associated_pow_of_mul_eq_pow
 [GCDMonoid α] {a b c : α} (hab : IsUnit (gcd a b)) {k : Nat} (h : a * b = c ^ k
) : exists d : α, Associa…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `gcd_isUnit_iff`：gcd_isUnit_iff (x y : R) : IsUnit (gcd x y) ↔ IsCoprime 
x y
-/
theorem exists_associated_pow_of_mul_eq_pow' {a b c : R} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ k) : ∃ d : R, Associated (d ^ k) a := by
  classical
  let := IsBezout.toGCDDomain R
  exact exists_associated_pow_of_mul_eq_pow ((gcd_isUnit_iff _ _).mpr hab) h
/-
**exists_associated_pow_of_associated_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_associated_pow_of_associated_pow_mul {a b c : R} (hab : IsCoprime a
 b) {k : Nat} (h : Associated (c ^ k) (a * b)) : exists d : R, Associated (d ^ k
) a
参数：hab : IsCoprime a b；h : Associated (c ^ k) (a * b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `exists_associated_pow_of_mul_eq_pow'`：exists_associated_pow_of_mul_eq_po
w' {a b c : R} (hab : IsCoprime a b) {k : Nat} (h : a * b = c ^ k) : exists d : 
R, Associated (d ^ k) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCoprime_mul_unit_right_right`：isCoprime_mul_unit_right_right (hu : IsU
nit x) (y z : R) : IsCoprime y (z * x) ↔ IsCoprime y z
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem exists_associated_pow_of_associated_pow_mul {a b c : R} (hab : IsCoprime a b) {k : ℕ}
    (h : Associated (c ^ k) (a * b)) : ∃ d : R, Associated (d ^ k) a := by
  obtain ⟨u, hu⟩ := h.symm
  exact exists_associated_pow_of_mul_eq_pow'
    ((isCoprime_mul_unit_right_right u.isUnit a b).mpr hab) <| mul_assoc a _ _ ▸ hu

end Bezout

variable [IsDomain R] [IsPrincipalIdealRing R]

/-
**isCoprime_of_irreducible_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_of_irreducible_dvd {x y : R} (nonzero : ¬(x = 0 ∧ y = 0)) (H : f
orall z : R, Irreducible z -> z ∣ x -> ¬z ∣ y) : IsCoprime x y
参数：nonzero : ¬(x = 0 ∧ y = 0)；H : forall z : R, Irreducible z -> z ∣ x -> ¬z ∣ y
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.isCoprime`：∀ {R : Type u} [inst : CommRing R] {x y : R} [Subm
odule.IsPrincipal (Ideal.span {x, y})], IsRelPrime x y → IsCoprime x y
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `WfDvdMonoid.isRelPrime_of_no_irreducible_factors`：isRelPrime_of_no_irred
ucible_factors {x y : α} (nonzero : ¬(x = 0 ∧ y = 0)) (H : forall z : α, Irreduc
ible z -> z ∣ x -> ¬z ∣ y) : IsRelPrim…
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
-/
theorem isCoprime_of_irreducible_dvd {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z : R, Irreducible z → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  (WfDvdMonoid.isRelPrime_of_no_irreducible_factors nonzero H).isCoprime
/-
**isCoprime_of_prime_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_of_prime_dvd {x y : R} (nonzero : ¬(x = 0 ∧ y = 0)) (H : forall 
z : R, Prime z -> z ∣ x -> ¬z ∣ y) : IsCoprime x y
参数：nonzero : ¬(x = 0 ∧ y = 0)；H : forall z : R, Prime z -> z ∣ x -> ¬z ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoprime_of_irreducible_dvd`：isCoprime_of_irreducible_dvd {x y : R} (no
nzero : ¬(x = 0 ∧ y = 0)) (H : forall z : R, Irreducible z -> z ∣ x -> ¬z ∣ y) :
 IsCoprime x y
· 使用定理 `Irreducible.prime`：Irreducible.prime [DecompositionMonoid M] {a : M} (ir
r : Irreducible a) : Prime a
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
-/
theorem isCoprime_of_prime_dvd {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z : R, Prime z → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  isCoprime_of_irreducible_dvd nonzero fun z zi ↦ H z zi.prime

end

section PrincipalOfPrime

namespace Ideal

variable (R) [Semiring R]

/-- `nonPrincipals R` is the set of all ideals of `R` that are not principal ideals. -/
/-
**Ideal.nonPrincipals** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ideal`。
形式化陈述：nonPrincipals
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`nonPrincipals R` is the set of all ideals of `R` that are not principal ideals.
-/
abbrev nonPrincipals := { I : Ideal R | ¬I.IsPrincipal }

variable {R}
/-
**Ideal.nonPrincipals_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：nonPrincipals_eq_empty_iff : nonPrincipals R = ∅ ↔ IsPrincipalIdealRing R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonPrincipals_eq_empty_iff : nonPrincipals R = ∅ ↔ IsPrincipalIdealRing R := by
  simp [Set.eq_empty_iff_forall_notMem, isPrincipalIdealRing_iff]

/-- Any chain in the set of non-principal ideals has an upper bound which is non-principal.
(Namely, the union of the chain is such an upper bound.)

If you want the existence of a maximal non-principal ideal see
`Ideal.exists_maximal_not_isPrincipal`. -/
/-
**Ideal.nonPrincipals_zorn** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：nonPrincipals_zorn (hR : ¬IsPrincipalIdealRing R) (c : Set (Ideal R)) (hs 
: c subseteq nonPrincipals R) (hchain : IsChain (· <= ·) c) : exists I in nonPri
ncipals R, forall J in c, J <= I
参数：hR : ¬IsPrincipalIdealRing R；c : Set (Ideal R)；hs : c subseteq nonPrincipals 
R；hchain : IsChain (· <= ·) c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_sSup_of_directed`：mem_sSup_of_directed {s : Set (Submodule
 R M)} {z} (hs : s.Nonempty) (hdir : DirectedOn (· <= ·) s) : z in sSup s ↔ exis
ts y in s, z in y
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
Any chain in the set of non-principal ideals has an upper bound which is non-pri
ncipal.
(Namely, the union of the chain is such an upper bound.)

If you want the existence of a maximal non-principal ideal see
`Ideal.exists_maximal_not_isPrincipal`.
-/
theorem nonPrincipals_zorn (hR : ¬IsPrincipalIdealRing R) (c : Set (Ideal R))
    (hs : c ⊆ nonPrincipals R) (hchain : IsChain (· ≤ ·) c) :
    ∃ I ∈ nonPrincipals R, ∀ J ∈ c, J ≤ I := by
  by_cases H : c.Nonempty
  · obtain ⟨K, hKmem⟩ := Set.nonempty_def.1 H
    refine ⟨sSup c, fun ⟨x, hx⟩ ↦ ?_, fun _ ↦ le_sSup⟩
    have hxmem : x ∈ sSup c := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨J, hJc, hxJ⟩ := (Submodule.mem_sSup_of_directed ⟨K, hKmem⟩ hchain.directedOn).1 hxmem
    have hsSupJ : sSup c = J := le_antisymm (by simp [hx, Ideal.span_le, hxJ]) (le_sSup hJc)
    exact hs hJc ⟨hsSupJ ▸ ⟨x, hx⟩⟩
  · simpa [Set.not_nonempty_iff_eq_empty.1 H, isPrincipalIdealRing_iff] using hR
/-
**Ideal.exists_maximal_not_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_maximal_not_isPrincipal (hR : ¬IsPrincipalIdealRing R) : exists I :
 Ideal R, Maximal (¬·.IsPrincipal) I
参数：hR : ¬IsPrincipalIdealRing R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le₀`：zorn_le₀ (s : Set α) (ih : forall c subseteq s, IsChain (· <= 
·) c -> exists ub in s, forall z in c, z <= ub) : exists m, Maximal (· in s) m
· 使用定理 `Ideal.nonPrincipals_zorn`：nonPrincipals_zorn (hR : ¬IsPrincipalIdealRing
 R) (c : Set (Ideal R)) (hs : c subseteq nonPrincipals R) (hchain : IsChain (· <
= ·) c) : exis…
-/
theorem exists_maximal_not_isPrincipal (hR : ¬IsPrincipalIdealRing R) :
    ∃ I : Ideal R, Maximal (¬·.IsPrincipal) I :=
  zorn_le₀ _ (nonPrincipals_zorn hR)

end Ideal

end PrincipalOfPrime

open Ideal in
/-
**span_singleton_inf_span_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：span_singleton_inf_span_singleton [EuclideanDomain R] [GCDMonoid R] (n m :
 R) : span {n} ⊓ span {m} = span {lcm n m}
参数：n m : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ext_iff`：∀ {α : Type u} [inst : Semiring α] {I J : Ideal α}, I = J
 ↔ ∀ (x : α), x ∈ I ↔ x ∈ J
· 使用定理 `Ideal.mem_inf`：mem_inf {I J : Ideal R} {x : R} : x in I ⊓ J ↔ x in I ∧ x
 in J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lcm_dvd_iff`：lcm_dvd_iff [GCDMonoid α] {a b c : α} : lcm a b ∣ c ↔ a ∣ c
 ∧ b ∣ c
-/
lemma span_singleton_inf_span_singleton [EuclideanDomain R] [GCDMonoid R] (n m : R) :
    span {n} ⊓ span {m} = span {lcm n m} := by
  rw [Ideal.ext_iff]
  intro x
  rw [Ideal.mem_inf]
  simp only [Ideal.mem_span_singleton]
  exact lcm_dvd_iff.symm
/-
**Ideal.exists_normalized_span_of_isPrincipal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.exists_normalized_span_of_isPrincipal {R : Type*} [CommSemiring R] [
NormalizationMonoid R] (I : Ideal R) [I.IsPrincipal] : exists x, normalize x = x
 ∧ I = Ideal.span {x}
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `normalize_idem`：normalize_idem (x : α) : normalize (normalize x) = norma
lize x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Ideal.exists_normalized_span_of_isPrincipal {R : Type*} [CommSemiring R]
    [NormalizationMonoid R] (I : Ideal R) [I.IsPrincipal] :
    ∃ x, normalize x = x ∧ I = Ideal.span {x} := by
  obtain ⟨x, rfl⟩ := ‹I.IsPrincipal›
  refine ⟨normalize x, normalize_idem x, le_antisymm ?_ ?_⟩ <;>
  simp [Ideal.mem_span_singleton]
