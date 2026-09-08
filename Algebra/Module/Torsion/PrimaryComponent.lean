/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# I-Primary Components of modules

Let `A` be a commutative ring and `I`, an ideal of `A`.
Given an `A`-Module `M` it's `I`-primary component is defined as
  $$M(I) := \bigcup_{i : \mathbb{N}} \text{torsionBySet A  M }  I ^ i.$$

For `P : HeightOneSpectrum A`, the main result of this file is that
  $$M \cong \bigoplus_{P} M(P).$$

## Main definitions

* `Ideal.primaryComponent` : The `I`-primary component of an `A`-module `M`.

-/

@[expose] public section

variable {A M M₁ M₂ : Type*} [CommRing A]

open IsDedekindDomain Submodule Module HeightOneSpectrum Set Function

namespace Ideal

variable (I : Ideal A)

section CommRing

section AddCommMonoid

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module A M] [Module A M₁]
    [Module A M₂]

open Set Function Submodule Module

variable (M)
/--
The `I`-primaryComponent component of a module `M` where `I` is an ideal of `A`. -/
/-
**Ideal.primaryComponent** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：primaryComponent : Submodule A M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `I`-primaryComponent component of a module `M` where `I` is an ideal of `A`.
-/
def primaryComponent : Submodule A M := ⨆ i : ℕ, torsionBySet A M ↑(I ^ i)
/-
**Ideal.primaryComponent_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：primaryComponent_mem (x : M) : x in primaryComponent M I ↔ exists n, x in 
torsionBySet A M ↑(I ^ n)
参数：x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [Nonempty ι] (S
 : ι -> Submodule R M) (H : Directed (· <= ·) S) {x} : x in iSup S ↔ exists i, x
 in S i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
-/
theorem primaryComponent_mem (x : M) :
    x ∈ primaryComponent M I ↔ ∃ n, x ∈ torsionBySet A M ↑(I ^ n) := by
  simp only [primaryComponent, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall]
  constructor
  · intro a
    rw [Submodule.mem_iSup_of_directed] at a
    · simpa using a
    · intro x y
      use max x y
      simp [torsionBySet_le_torsionBySet_pow]
  · aesop (add safe Submodule.mem_iSup_of_mem)
/-
**Ideal.primaryComponent_map_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：primaryComponent_map_mem (φ : M₁ ->ₗ[A] M₂) (c : primaryComponent M₁ I) : 
φ c in primaryComponent M₂ I
参数：φ : M₁ ->ₗ[A] M₂；c : primaryComponent M₁ I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem primaryComponent_map_mem (φ : M₁ →ₗ[A] M₂) (c : primaryComponent M₁ I) :
    φ c ∈ primaryComponent M₂ I := by
  obtain ⟨c, hc⟩ := c
  simp only [primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall,
    ← map_smul] at ⊢ hc
  obtain ⟨n, hn⟩ := hc
  use n
  grind

/-- Given an A-linear map between M₁ and M₂, `primaryComponent.map` is the
restriction to the I-primaryComponent components of M₁ and M₂. -/
@[simps!]
/-
**Ideal.primaryComponent.map** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.primaryComponent`。
形式化陈述：{A : Type u_1} →   {M₁ : Type u_3} →     {M₂ : Type u_4} →       [inst : C
ommRing A] →         (I : Ideal A) →           [inst_1 : AddCommMonoid M₁] →    
         [inst_2 : AddCommMonoid M₂] →               [inst_3 : _root_.Module A M
₁] →                 [inst_4 : _root_.Module A M₂] →                   (M₁ →ₗ[A]
 M₂) → ↥(Ideal.primaryComponent M₁ I) →ₗ[A] ↥(Ideal.primaryComponent M₂ I)
参数：I : Ideal A；M₁ →ₗ[A] M₂；Ideal.primaryComponent M₁ I；Ideal.primaryComponent M₂
 I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an A-linear map between M₁ and M₂, `primaryComponent.map` is the
restriction to the I-primaryComponent components of M₁ and M₂.
-/
def primaryComponent.map (φ : M₁ →ₗ[A] M₂) : primaryComponent M₁ I →ₗ[A] primaryComponent M₂ I :=
  (φ.domRestrict (primaryComponent M₁ I)).codRestrict (primaryComponent M₂ I) (fun c ↦
    by simpa only [LinearMap.domRestrict_apply] using primaryComponent_map_mem I φ c)
/-
**Ideal.primaryComponent.map_ker_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.primaryComp
onent`。
形式化陈述：∀ {A : Type u_1} {M₁ : Type u_3} {M₂ : Type u_4} [inst : CommRing A] (I : 
Ideal A) [inst_1 : AddCommMonoid M₁]   [inst_2 : AddCommMonoid M₂] [inst_3 : _ro
ot_.Module A M₁] [inst_4 : _root_.Module A M₂] (φ : M₁ →ₗ[A] M₂),   Submodule.ma
p (Ideal.primaryComponent M₁ I).subtype (Ideal.primaryComponent.map I φ).ker =  
   Submodule.map φ.ker.subtype (Ideal.primaryComponent (↥φ.ker) I)
参数：I : Ideal A；φ : M₁ →ₗ[A] M₂；Ideal.primaryComponent M₁ I；Ideal.primaryComponen
t.map I φ；Ideal.primaryComponent (↥φ.ker) I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LinearMap.ker_codRestrict`：ker_codRestrict (p : Submodule R₂ M₂) (f : M 
->ₛₗ[τ₁₂] M₂) (hf) : ker (codRestrict p f hf) = ker f
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem primaryComponent.map_ker_eq (φ : M₁ →ₗ[A] M₂) :
    (primaryComponent.map I φ).ker.map (primaryComponent M₁ I).subtype =
      (primaryComponent φ.ker I).map φ.ker.subtype := by
  aesop (add norm [map, Subtype.ext_iff, primaryComponent_mem])
/-
**Ideal.primaryComponent_torsionBySet_eq_inf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：primaryComponent_torsionBySet_eq_inf (I : Ideal A) : (primaryComponent (to
rsionBySet A M ↑I) I).map (Submodule.subtype _) = primaryComponent M I ⊓ torsion
BySet A M ↑I
参数：I : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem primaryComponent_torsionBySet_eq_inf (I : Ideal A) :
    (primaryComponent (torsionBySet A M ↑I) I).map (Submodule.subtype _) =
    primaryComponent M I ⊓ torsionBySet A M ↑I := by
  ext x
  simp [primaryComponent_mem]
/-
**Ideal.primaryComponent_torsionBySet_of_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `Id
eal`。
形式化陈述：primaryComponent_torsionBySet_of_isCoprime (J : Ideal A) (hD : IsCoprime I
 J) : primaryComponent (torsionBySet A M J) I = ⊥
参数：J : Ideal A；hD : IsCoprime I J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.disjoint_torsionBySet_ideal`：disjoint_torsionBySet_ideal {P Q 
: Ideal R} (hc : P ⊔ Q = ⊤) : Disjoint (torsionBySet R M ↑(P)) (torsionBySet R M
 ↑(Q))
· 使用定理 `Ideal.pow_sup_eq_top`：pow_sup_eq_top [I.IsTwoSided] {n : Nat} (h : I ⊔ J
 = ⊤) : I ^ n ⊔ J = ⊤
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsCoprime.sup_eq`：∀ {R : Type u} [inst : CommSemiring R] {I J : Ideal R}
, IsCoprime I J → I ⊔ J = ⊤
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem primaryComponent_torsionBySet_of_isCoprime (J : Ideal A) (hD : IsCoprime I J) :
    primaryComponent (torsionBySet A M J) I = ⊥ := by
  have (n : ℕ) : Disjoint (torsionBySet A M ↑(I ^ n)) (torsionBySet A M ↑J) :=
    Submodule.disjoint_torsionBySet_ideal (M := M) (Ideal.pow_sup_eq_top hD.sup_eq)
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective (torsionBySet A M ↑J))
  ext x
  simp only [mem_map, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.map_bot, Submodule.mem_bot]
  refine ⟨fun ⟨⟨n, _⟩, _⟩ ↦ ?_, by simp_all⟩
  specialize this n
  simp_all [disjoint_def]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup M] [Module A M]

open Submodule in
/-
**Ideal.primaryComponent_sup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：primaryComponent_sup (N₁ N₂ : Submodule A M) (hD : Disjoint N₁ N₂) : (prim
aryComponent ↥(N₁ ⊔ N₂) I).map (N₁ ⊔ N₂).subtype = (primaryComponent N₁ I).map N
₁.subtype ⊔ (primaryComponent N₂ I).map N₂.subtype
参数：N₁ N₂ : Submodule A M；hD : Disjoint N₁ N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.disjoint_iff_add_eq_zero`：disjoint_iff_add_eq_zero {M R : Type
*} [Ring R] [AddCommGroup M] [Module R M] {N₁ N₂ : Submodule R M} : Disjoint N₁ 
N₂ ↔ forall {x y : M}, x…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem primaryComponent_sup (N₁ N₂ : Submodule A M) (hD : Disjoint N₁ N₂) :
    (primaryComponent ↥(N₁ ⊔ N₂) I).map (N₁ ⊔ N₂).subtype =
    (primaryComponent N₁ I).map N₁.subtype ⊔ (primaryComponent N₂ I).map N₂.subtype := by
  ext x
  simp_all only [mem_map, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
    Subtype.forall, subtype_apply, Subtype.exists, SetLike.mk_smul_mk, mk_eq_zero, exists_and_left,
    exists_prop, exists_eq_right_right, Submodule.mem_sup]
  constructor
  · rintro ⟨⟨w, h⟩, ⟨y, hy, z, hz, rfl⟩⟩
    refine ⟨y, ⟨⟨w, fun a ha ↦ ?_⟩, by simp [hy]⟩, z, ⟨⟨w, fun a ha ↦ ?_⟩, by simp [hz]⟩, rfl⟩
    · exact ((Submodule.disjoint_iff_add_eq_zero.mp hD) (Submodule.smul_mem N₁ a hy)
        (Submodule.smul_mem N₂ a hz) (h a ha ▸ (smul_add a y z).symm)).1
    · exact ((Submodule.disjoint_iff_add_eq_zero.mp hD) (Submodule.smul_mem N₁ a hy)
        (Submodule.smul_mem N₂ a hz) (h a ha ▸ (smul_add a y z).symm)).2
  · rintro ⟨y, ⟨⟨n₁, hy⟩, hymem⟩, z, ⟨⟨n₂, hz⟩, hzmem⟩, rfl⟩
    constructor
    · use (max n₁ n₂)
      intro a ha
      specialize hy a (Ideal.pow_le_pow_right (by simp : n₁ ≤ max n₁ n₂) ha)
      specialize hz a (Ideal.pow_le_pow_right (by simp : n₂ ≤ max n₁ n₂) ha)
      aesop
    · use y, hymem, z, hzmem

section IsDedekindDomain

variable [IsDedekindDomain A]

open scoped nonZeroDivisors

/-
**Ideal.iSup_primaryComponent_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：iSup_primaryComponent_eq_top (h : IsTorsion A M) : ⨆ P : HeightOneSpectrum
 A, primaryComponent M (P : Ideal A) = ⊤
参数：h : IsTorsion A M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.torsionBySet_eq_torsionBySet_span`：torsionBySet_eq_torsionBySe
t_span : torsionBySet R M s = torsionBySet R M (Ideal.span s)
· 使用定理 `Submodule.torsionBySet_singleton_eq`：torsionBySet_singleton_eq : torsion
BySet R M {a} = torsionBy R M a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.hasFiniteMulSupport`：hasFiniteMulSupport {I : Ideal R} (hI : I != 
0) : HasFiniteMulSupport fun v : HeightOneSpectrum R => v.maxPowDividing I
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsCoprime.sup_eq`：∀ {R : Type u} [inst : CommSemiring R] {I J : Ideal R}
, IsCoprime I J → I ⊔ J = ⊤
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne`：isCoprime_pow_of
_ne (P Q : HeightOneSpectrum R) (hPQ : P != Q) (n m : Nat) : IsCoprime (P.asIdea
l ^ n) (Q.asIdeal ^ m)
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
（共 37 条，此处仅展示前 30 条）
-/
theorem iSup_primaryComponent_eq_top (h : IsTorsion A M) :
    ⨆ P : HeightOneSpectrum A, primaryComponent M (P : Ideal A) = ⊤ := by
  rw [eq_top_iff']
  intro x
  obtain ⟨⟨a : A, ha : a ∈ A⁰⟩, hmem : a • x = 0⟩ := h (x := x)
  replace hmem : x ∈ torsionBySet A M (span {a}) := by
    simp_all [← torsionBySet_eq_torsionBySet_span {a}]
  have ha0 : span {a} ≠ ⊥ := by simpa using nonZeroDivisors.ne_zero ha
  rw [← iInf_maxPowDividing_eq ha0] at hmem
  let : Fintype (mulSupport fun v : HeightOneSpectrum A => v.maxPowDividing (span {a})) :=
    Finite.fintype (hasFiniteMulSupport ha0)
  let S := (mulSupport fun v : HeightOneSpectrum A => v.maxPowDividing (span {a})).toFinset
  have : (⨅ i : HeightOneSpectrum A, i.maxPowDividing (span {a})) =
      (⨅ i ∈ S, i.maxPowDividing (span {a})) := by
    ext x
    constructor
    · aesop
    · simp only [mem_iInf]
      intro h i
      by_cases htop : i.maxPowDividing (span {a}) = ⊤ <;> simp_all [S]
  have hPairwise : (S : Set (HeightOneSpectrum _)).Pairwise
      fun i j ↦ i.maxPowDividing (span {a}) ⊔ j.maxPowDividing (span {a}) = ⊤ :=
    fun r hr s hs hrs ↦ (isCoprime_pow_of_ne _ _ hrs _ _).sup_eq
  rw [this, ← iSup_torsionBySet_ideal_eq_torsionBySet_iInf hPairwise] at hmem
  revert x
  rw [← SetLike.le_def]
  refine iSup_mono (fun P x hxmem ↦ ?_)
  by_cases hPS : P ∈ S
  · simp_all only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, mem_toFinset, mem_mulSupport,
      one_eq_top, primaryComponent_mem, mem_torsionBySet_iff, SetLike.coe_sort_coe,
      Subtype.forall, iSup_pos, S]
    exact ⟨(Associates.mk P.asIdeal).count (Associates.mk (span {a})).factors, fun _ b ↦ hxmem _ b⟩
  · simp_all

variable (A M) in
/-
**Ideal.iSupIndep_primaryComponent** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：iSupIndep_primaryComponent : iSupIndep fun P : HeightOneSpectrum A => prim
aryComponent M (P : Ideal A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`：iSupIndep_iff_finsetSum_eq_
zero_imp_eq_zero (p : ι -> Submodule R N) : iSupIndep p ↔ forall (s : Finset ι) 
(v : ι -> N), (forall i in s, v i…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `iSupIndep_iff_supIndep`：iSupIndep_iff_supIndep {ι : Type*} {f : ι -> α} 
: iSupIndep f ↔ forall (s : Finset ι), s.SupIndep f
· 使用定理 `Submodule.instIsCompactlyGenerated`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   IsCom
pactlyGenerated (Submodu…
· 使用定理 `Submodule.supIndep_torsionBySet_ideal`：supIndep_torsionBySet_ideal (hp :
 (S : Set ι).Pairwise fun i j => p i ⊔ p j = ⊤) : S.SupIndep fun i => torsionByS
et R M p i
· 使用定理 `IsCoprime.sup_eq`：∀ {R : Type u} [inst : CommSemiring R] {I J : Ideal R}
, IsCoprime I J → I ⊔ J = ⊤
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne`：isCoprime_pow_of
_ne (P Q : HeightOneSpectrum R) (hPQ : P != Q) (n m : Nat) : IsCoprime (P.asIdea
l ^ n) (Q.asIdeal ^ m)
· 使用定理 `Submodule.torsionBySet_le_torsionBySet_pow`：torsionBySet_le_torsionBySet
_pow (i j : Nat) (h : i <= j) (I : Ideal R) : torsionBySet R M ↑(I ^ i) <= torsi
onBySet R M ↑(I ^ j)
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem iSupIndep_primaryComponent :
    iSupIndep fun P : HeightOneSpectrum A => primaryComponent M (P : Ideal A) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s p hmem hsum
  simp only [primaryComponent_mem] at hmem
  choose! f hmem using hmem
  let m := s.sup f
  have hSupIndep : iSupIndep fun i : HeightOneSpectrum A ↦ torsionBySet A M ↑(i.asIdeal ^ m) := by
    rw [iSupIndep_iff_supIndep]
    exact fun _ ↦ supIndep_torsionBySet_ideal
      fun _ _ _ _ hPQ ↦ (isCoprime_pow_of_ne _ _ hPQ _ _).sup_eq
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hSupIndep
  apply hSupIndep _ _ ?_ hsum
  exact fun P hP ↦ torsionBySet_le_torsionBySet_pow _ _ (Finset.le_sup hP) _ (hmem P hP)
/-
**Ideal.primaryComponent.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.primary
Component`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] [IsDedekindDomain A] {M₁ : Type u_5} 
{M₂ : Type u_6} [inst_2 : AddCommGroup M₁]   [inst_3 : AddCommGroup M₂] [inst_4 
: _root_.Module A M₁] [inst_5 : _root_.Module A M₂],   Module.IsTorsion A M₁ →  
   ∀ (P : IsDedekindDomain.HeightOneSpectrum A) (φ : M₁ →ₗ[A] M₂),       Functio
n.Surjective ⇑φ → Function.Surjective ⇑(Ideal.primaryComponent.map P.asIdeal φ)
参数：P : IsDedekindDomain.HeightOneSpectrum A；φ : M₁ →ₗ[A] M₂；Ideal.primaryCompone
nt.map P.asIdeal φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.iSup_primaryComponent_eq_top`：iSup_primaryComponent_eq_top (h : Is
Torsion A M) : ⨆ P : HeightOneSpectrum A, primaryComponent M (P : Ideal A) = ⊤
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Ideal.primaryComponent.map_apply_coe`：∀ {A : Type u_1} {M₁ : Type u_3} {
M₂ : Type u_4} [inst : CommRing A] (I : Ideal A) [inst_1 : AddCommMonoid M₁]   [
inst_2 : AddCommMonoid M₂]…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Ideal.iSupIndep_primaryComponent`：iSupIndep_primaryComponent : iSupIndep
 fun P : HeightOneSpectrum A => primaryComponent M (P : Ideal A)
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Ideal.primaryComponent_map_mem`：primaryComponent_map_mem (φ : M₁ ->ₗ[A] 
M₂) (c : primaryComponent M₁ I) : φ c in primaryComponent M₂ I
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `Finset.sum_eq_add_sum_sdiff_singleton`：∀ {ι : Type u_1} {M : Type u_3} [
inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} (i : ι) (f : ι →
 M),   (i ∉ s → f i = 0) → …
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
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
-/
theorem primaryComponent.map_surjective {M₁ M₂ : Type*}
    [AddCommGroup M₁] [AddCommGroup M₂] [Module A M₁] [Module A M₂] (hM₁ : IsTorsion A M₁)
    (P : HeightOneSpectrum A) (φ : M₁ →ₗ[A] M₂) (hf : Surjective φ) :
    Surjective (primaryComponent.map P.asIdeal φ) := by
  classical
  rintro ⟨y, hy⟩
  obtain ⟨b, rfl⟩ : ∃ a, φ a = y := hf y
  obtain ⟨f, hf⟩ : ∃ f : Π₀ i : HeightOneSpectrum A, primaryComponent M₁ i.asIdeal,
      (DFinsupp.lsum ℕ fun i : HeightOneSpectrum A ↦
      (primaryComponent M₁ i.asIdeal).subtype) f = b := by
    simp only [← mem_iSup_iff_exists_dfinsupp, iSup_primaryComponent_eq_top hM₁, mem_top]
  refine ⟨f P, Subtype.ext ?_⟩
  simp only [map_apply_coe]
  rw [eq_comm, ← sub_eq_zero]
  refine (Submodule.disjoint_def.mp (iSupIndep_primaryComponent A M₂ P)) _ ?_ ?_
  · exact Submodule.sub_mem _ hy (primaryComponent_map_mem _ _ _)
  · have hdiff : φ b - φ ↑(f P) = ∑ Q ∈ f.support \ {P}, φ ↑(f Q) := by
      rw [sub_eq_iff_eq_add',
        ← Finset.sum_eq_add_sum_sdiff_singleton P (fun P ↦ φ (f P)) (by aesop)]
      simpa [DFinsupp.sumAddHom_apply, DFinsupp.sum] using congr(φ $hf).symm
    rw [hdiff]
    exact Submodule.sum_mem _ fun Q hQ ↦ Submodule.mem_iSup_of_mem Q <|
        Submodule.mem_iSup_of_mem (by grind) (primaryComponent_map_mem _ _ _)

end IsDedekindDomain

end AddCommGroup

end CommRing

end Ideal

