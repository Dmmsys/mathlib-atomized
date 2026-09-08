/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom, Xavier Roblot
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Extension of fractional ideals

This file defines the extension of a fractional ideal along a ring homomorphism.

## Main definitions

* `FractionalIdeal.extended`: Let `A` and `B` be commutative rings with respective localizations
  `IsLocalization M K` and `IsLocalization N L`. Let `f : A →+* B` be a ring homomorphism with
  `hf : M ≤ Submonoid.comap f N`. If `I : FractionalIdeal M K`, then the extension of `I` along
  `f` is `extended L hf I : FractionalIdeal N L`.
* `FractionalIdeal.extendedHom'`: The ring homomorphism version of `FractionalIdeal.extended`.
* `FractionalIdeal.extendedHom`: For `A ⊆ B` an extension of domains, the ring homomorphism that
  sends a fractional ideal of `A` to a fractional ideal of `B`.

## Main results

* `FractionalIdeal.extendedHom_injective`: the map `FractionalIdeal.extendedHom` is injective.
* `FractionalIdeal.extended_extended`: extending fractional ideals is compatible with composition
  of ring homomorphisms.
* `FractionalIdeal.extendedHom'_comp`: the homomorphisms induced by extension of fractional
  ideals compose in towers.
* `Ideal.map_algebraMap_injective`: For `A ⊆ B` an extension of Dedekind domains, the map that
  sends an ideal `I` of `A` to `I·B` is injective.

## Tags

fractional ideal, fractional ideals, extended, extension
-/

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- This is why this section is `noncomputable`.
-- See https://github.com/leanprover/lean4/issues/14084.
@[expose] public noncomputable section

open IsLocalization FractionalIdeal Module Submodule

namespace FractionalIdeal

section RingHom

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] {f : A →+* B}
variable {K : Type*} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
variable (L : Type*) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
variable (hf : M ≤ Submonoid.comap f N)
variable (I : FractionalIdeal M K) (J : FractionalIdeal M K)

/-- Given commutative rings `A` and `B` with respective localizations `IsLocalization M K` and
`IsLocalization N L`, and a ring homomorphism `f : A →+* B` satisfying `M ≤ Submonoid.comap f N`, a
fractional ideal `I` of `A` can be extended along `f` to a fractional ideal of `B`. -/
/-
**FractionalIdeal.extended** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：extended (I : FractionalIdeal M K) : FractionalIdeal N L where val
参数：I : FractionalIdeal M K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given commutative rings `A` and `B` with respective localizations `IsLocalizatio
n M K` and
`IsLocalization N L`, and a ring homomorphism `f : A →+* B` satisfying `M ≤ Subm
onoid.comap f N`, a
fractional ideal `I` of `A` can be extended along `f` to a fractional ideal of `
B`.
-/
def extended (I : FractionalIdeal M K) : FractionalIdeal N L where
  val := span B <| (IsLocalization.map (S := K) L f hf) '' I
  property := by
    have ⟨a, ha, frac⟩ := I.isFractional
    refine ⟨f a, hf ha, fun b hb ↦ ?_⟩
    refine span_induction (fun x hx ↦ ?_) ⟨0, by simp⟩
      (fun x y _ _ hx hy ↦ smul_add (f a) x y ▸ isInteger_add hx hy) (fun b c _ hc ↦ ?_) hb
    · rcases hx with ⟨k, kI, rfl⟩
      obtain ⟨c, hc⟩ := frac k kI
      exact ⟨f c, by simp [← IsLocalization.map_smul, ← hc]⟩
    · rw [← smul_assoc, smul_eq_mul, mul_comm (f a), ← smul_eq_mul, smul_assoc]
      exact isInteger_smul hc

local notation "map_f" => (IsLocalization.map (S := K) L f hf)
/-
**FractionalIdeal.mem_extended_iff** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_extended_iff (x : L) : x in I.extended L hf ↔ x in span B (map_f '' I)
参数：x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma mem_extended_iff (x : L) : x ∈ I.extended L hf ↔ x ∈ span B (map_f '' I) := by
  constructor <;> { intro hx; simpa }

@[simp]
/-
**FractionalIdeal.coe_extended_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdea
l`。
形式化陈述：coe_extended_eq_span : I.extended L hf = span B (map_f '' I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_extended_eq_span : I.extended L hf = span B (map_f '' I) := by
  ext; simp [mem_coe, mem_extended_iff]

@[simp]
/-
**FractionalIdeal.extended_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：extended_zero : extended L hf (0 : FractionalIdeal M K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用引理 `FractionalIdeal.coe_extended_eq_span`：coe_extended_eq_span : I.extended 
L hf = span B (map_f '' I)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extended_zero : extended L hf (0 : FractionalIdeal M K) = 0 :=
  have : ((0 : FractionalIdeal M K) : Set K) = {0} := by ext; simp
  coeToSubmodule_injective (by simp [this])

variable {I}
/-
**FractionalIdeal.extended_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：extended_ne_zero [IsDomain B] (hf' : Function.Injective f) (hI : I != 0) (
hN : 0 ∉ N) : extended L hf I != 0
参数：hf' : Function.Injective f；hI : I != 0；hN : 0 ∉ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `FractionalIdeal.coe_extended_eq_span`：coe_extended_eq_span : I.extended 
L hf = span B (map_f '' I)
· 使用定理 `FractionalIdeal.coe_zero`：coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : S
ubmodule R P)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `IsLocalization.map_injective_of_injective'`：map_injective_of_injective' 
{f : R ->+* S} {Rₘ : Type*} [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ] (
Sₘ : Type*) {N : Submonoid S} [C…
-/
theorem extended_ne_zero [IsDomain B] (hf' : Function.Injective f) (hI : I ≠ 0) (hN : 0 ∉ N) :
    extended L hf I ≠ 0 := by
  simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    not_forall]
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ I, x ≠ 0 := by simpa [ne_eq, eq_zero_iff] using hI
  refine ⟨x, hx₁, ?_⟩
  exact (map_ne_zero_iff _ (IsLocalization.map_injective_of_injective' _ _ _ _ hN hf')).mpr hx₂

@[simp]
/-
**FractionalIdeal.extended_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdea
l`。
形式化陈述：extended_eq_zero_iff [IsDomain B] (hf' : Function.Injective f) (hN : 0 ∉ N
) : extended L hf I = 0 ↔ I = 0
参数：hf' : Function.Injective f；hN : 0 ∉ N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `FractionalIdeal.extended_ne_zero`：extended_ne_zero [IsDomain B] (hf' : F
unction.Injective f) (hI : I != 0) (hN : 0 ∉ N) : extended L hf I != 0
· 使用定理 `FractionalIdeal.extended_zero`：extended_zero : extended L hf (0 : Fracti
onalIdeal M K) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem extended_eq_zero_iff [IsDomain B] (hf' : Function.Injective f) (hN : 0 ∉ N) :
    extended L hf I = 0 ↔ I = 0 := by
  refine ⟨?_, fun h ↦ h ▸ extended_zero _ _⟩
  contrapose!
  exact fun h ↦ extended_ne_zero L hf hf' h hN

variable (I)

@[simp]
/-
**FractionalIdeal.extended_one** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：extended_one : extended L hf (1 : FractionalIdeal M K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.linearMap_apply`：linearMap_apply (r : R) : Algebra.linearMap R A
 r = algebraMap R A r
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用引理 `FractionalIdeal.zero_mem`：zero_mem (I : FractionalIdeal S P) : 0 in I
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `FractionalIdeal.one_mem_one`：one_mem_one : (1 : P) in (1 : FractionalIde
al S P)
-/
theorem extended_one : extended L hf (1 : FractionalIdeal M K) = 1 := by
  refine coeToSubmodule_injective <| Submodule.ext fun x ↦ ⟨fun hx ↦ span_induction
    ?_ (zero_mem _) (fun y z _ _ hy hz ↦ add_mem hy hz) (fun b y _ hy ↦ smul_mem _ b hy) hx, ?_⟩
  · rintro ⟨b, _, rfl⟩
    rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    exact smul_mem _ _ <| subset_span ⟨1, by simpa using one_mem_one⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, ha, by rw [Algebra.linearMap_apply, Algebra.linearMap_apply, map_eq]⟩
/-
**FractionalIdeal.extended_le_one_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Fractiona
lIdeal`。
形式化陈述：extended_le_one_of_le_one (hI : I <= 1) : extended L hf I <= 1
参数：hI : I <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.le_one_iff_exists_coeIdeal`：le_one_iff_exists_coeIdeal {
J : FractionalIdeal S P} : J <= (1 : FractionalIdeal S P) ↔ exists I : Ideal R, 
↑I = J
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.sum_smul_mem`：sum_smul_mem {t : Finset ι} {f : ι -> M} (r : ι 
-> R) (hyp : forall c in t, f c in p) : (∑ i in t, r i • f i) in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem extended_le_one_of_le_one (hI : I ≤ 1) : extended L hf I ≤ 1 := by
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp hI
  intro x hx
  simp only [mem_extended_iff, mem_span_image_iff_exists_fun] at hx
  obtain ⟨s, hs, c, rfl⟩ := hx
  refine Submodule.sum_smul_mem _ _ fun ⟨x, hx⟩ h ↦ ?_
  obtain ⟨a, ha, rfl⟩ := hI (hs hx)
  exact ⟨f a, by simp [map_eq]⟩
/-
**FractionalIdeal.one_le_extended_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Fractiona
lIdeal`。
形式化陈述：one_le_extended_of_one_le (hI : 1 <= I) : 1 <= extended L hf I
参数：hI : 1 <= I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.one_le`：one_le {I : FractionalIdeal S P} : 1 <= I ↔ (1 :
 P) in I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `FractionalIdeal.mem_extended_iff`：mem_extended_iff (x : L) : x in I.exte
nded L hf ↔ x in span B (map_f '' I)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem one_le_extended_of_one_le (hI : 1 ≤ I) : 1 ≤ extended L hf I := by
  rw [one_le] at hI ⊢
  exact (mem_extended_iff _ _ _ _).mpr <| subset_span ⟨1, hI, by rw [map_one]⟩
/-
**FractionalIdeal.extended_add** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：extended_add : (I + J).extended L hf = (I.extended L hf) + (J.extended L h
f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.coe_extended_eq_span`：coe_extended_eq_span : I.extended 
L hf = span B (map_f '' I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_eq_span`：span_eq_span (hs : s subseteq span R t) (ht : t 
subseteq span R s) : span R s = span R t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_add`：mem_add (I J : FractionalIdeal S P) (x : P) : x
 in I + J ↔ exists i in I, exists j in J, i + j = x
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.mem_union_right`：mem_union_right {x : α} {b : Set α} (a : Set α) : x
 in b -> x in a union b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `FractionalIdeal.zero_mem`：zero_mem (I : FractionalIdeal S P) : 0 in I
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem extended_add : (I + J).extended L hf = (I.extended L hf) + (J.extended L hf) := by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_add, Submodule.add_eq_sup, ← span_union, ← Set.image_union]
  apply Submodule.span_eq_span
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨i, hi, j, hj, rfl⟩ := (mem_add I J y).mp <| SetLike.mem_coe.mp hy
    rw [map_add]
    exact add_mem (Submodule.subset_span ⟨i, Set.mem_union_left _ hi, by simp⟩)
      (Submodule.subset_span ⟨j, Set.mem_union_right _ hj, by simp⟩)
  · rintro _ ⟨y, hy, rfl⟩
    suffices y ∈ I + J from SetLike.mem_coe.mpr <| Submodule.subset_span ⟨y, by simp [this]⟩
    exact hy.elim (fun h ↦ (mem_add I J y).mpr ⟨y, h, 0, zero_mem J, add_zero y⟩)
      (fun h ↦ (mem_add I J y).mpr ⟨0, zero_mem I, y, h, zero_add y⟩)
/-
**FractionalIdeal.extended_mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：extended_mul : (I * J).extended L hf = (I.extended L hf) * (J.extended L h
f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `FractionalIdeal.coeToSubmodule_injective`：coeToSubmodule_injective : Fun
ction.Injective (fun (I : FractionalIdeal S P) => (I : Submodule R P))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.coe_extended_eq_span`：coe_extended_eq_span : I.extended 
L hf = span B (map_f '' I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `FractionalIdeal.coe_mul`：coe_mul (I J : FractionalIdeal S P) : (↑(I * J)
 : Submodule R P) = I * J
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `Submodule.span_eq_span`：span_eq_span (hs : s subseteq span R t) (ht : t 
subseteq span R s) : span R s = span R t
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_mul`：mem_mul : a in s * t ↔ exists x in s, exists y in t, x * y 
= a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
（共 35 条，此处仅展示前 30 条）
-/
theorem extended_mul : (I * J).extended L hf = (I.extended L hf) * (J.extended L hf) := by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_mul, span_mul_span]
  refine Submodule.span_eq_span (fun _ h ↦ ?_) (fun _ h ↦ ?_)
  · rcases h with ⟨x, hx, rfl⟩
    replace hx : x ∈ (I : Submodule A K) * (J : Submodule A K) := coe_mul I J ▸ hx
    rw [Submodule.mul_eq_span_mul_set] at hx
    refine span_induction (fun y hy ↦ ?_) (by simp) (fun y z _ _ hy hz ↦ ?_)
      (fun a y _ hy ↦ ?_) hx
    · rcases Set.mem_mul.mp hy with ⟨i, hi, j, hj, rfl⟩
      exact subset_span <| Set.mem_mul.mpr
        ⟨map_f i, ⟨i, hi, by simp⟩, map_f j, ⟨j, hj, by simp⟩, by simp⟩
    · exact map_add map_f y z ▸ Submodule.add_mem _ hy hz
    · rw [Algebra.smul_def, map_mul, map_eq, ← Algebra.smul_def]
      exact smul_mem _ (f a) hy
  · rcases Set.mem_mul.mp h with ⟨y, ⟨i, hi, rfl⟩, z, ⟨j, hj, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨i * j, mul_mem_mul hi hj, by simp⟩

/-- Pointwise compatibility of extension of fractional ideals with composition of ring
homomorphisms. See `FractionalIdeal.extendedHom'_comp` for the corresponding statement as an
equality of homomorphisms. -/
/-
**FractionalIdeal.extended_extended** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：extended_extended {C W : Type*} [CommRing C] [CommRing W] [Algebra C W] {P
 : Submonoid C} [IsLocalization P W] {g : B ->+* C} (hg : N <= Submonoid.comap g
 P) : (I.extended L hf).extended W hg = I.extended W (f
参数：hg : N <= Submonoid.comap g P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submonoid.monotone_comap`：monotone_comap {f : F} : Monotone (comap f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coeToSubmodule_inj`：coeToSubmodule_inj {I J : Fractional
Ideal S P} : (I : Submodule R P) = J ↔ I = J
· 使用引理 `FractionalIdeal.coe_extended_eq_span`：coe_extended_eq_span : I.extended 
L hf = span B (map_f '' I)
· 使用定理 `Submodule.span_eq_span`：span_eq_span (hs : s subseteq span R t) (ht : t 
subseteq span R s) : span R s = span R t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `FractionalIdeal.mem_extended_iff`：mem_extended_iff (x : L) : x in I.exte
nded L hf ↔ x in span B (map_f '' I)
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `IsLocalization.map_map`：map_map {A : Type*} [CommSemiring A] {U : Submon
oid A} {W} [CommSemiring W] [Algebra A W] [IsLocalization U W] {l : P ->+* A} (h
l : T <= U.c…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `IsLocalization.map_smul`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] {P
 : Type u_3} …
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
Pointwise compatibility of extension of fractional ideals with composition of ri
ng
homomorphisms. See `FractionalIdeal.extendedHom'_comp` for the corresponding sta
tement as an
equality of homomorphisms.
-/
theorem extended_extended {C W : Type*} [CommRing C] [CommRing W] [Algebra C W]
    {P : Submonoid C} [IsLocalization P W] {g : B →+* C} (hg : N ≤ Submonoid.comap g P) :
      (I.extended L hf).extended W hg =
        I.extended W (f := g.comp f) (hf.trans (Submonoid.monotone_comap hg)) := by
  rw [← coeToSubmodule_inj, coe_extended_eq_span, coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ span B (IsLocalization.map L f hf '' (I : Set K)) :=
      (mem_extended_iff L hf I x).1 hx
    refine span_induction (fun y hy ↦ ?_) (by simp) (fun y z _ _ hy hz ↦ ?_) (fun b y _ hy ↦ ?_) hx'
    · rcases hy with ⟨z, hz, rfl⟩
      exact Submodule.subset_span ⟨z, hz, by rw [IsLocalization.map_map]⟩
    · rw [map_add]
      exact add_mem hy hz
    · rw [IsLocalization.map_smul]
      exact smul_mem _ (g b) hy
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨IsLocalization.map L f hf x, ?_, ?_⟩
    · exact (mem_extended_iff L hf I _).2 <| Submodule.subset_span ⟨x, hx, rfl⟩
    · rw [IsLocalization.map_map]

@[simp]
/-
**FractionalIdeal.extended_coeIdeal_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Fractional
Ideal`。
形式化陈述：extended_coeIdeal_eq_map (I₀ : Ideal A) : (I₀ : FractionalIdeal M K).exten
ded L hf = (I₀.map f : FractionalIdeal N L)
参数：I₀ : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   (I : Ideal R), I
deal…
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coeToSubmodule_inj`：coeToSubmodule_inj {I J : Fractional
Ideal S P} : (I : Submodule R P) = J ↔ I = J
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `FractionalIdeal.coe_coeIdeal`：coe_coeIdeal (I : Ideal R) : ((I : Fractio
nalIdeal S P) : Submodule R P) = coeSubmodule P I
· 使用定理 `IsLocalization.coeSubmodule_span`：coeSubmodule_span (s : Set R) : coeSub
module S (Ideal.span s) = Submodule.span R (algebraMap R S '' s)
· 使用引理 `FractionalIdeal.coe_extended_eq_span`：coe_extended_eq_span : I.extended 
L hf = span B (map_f '' I)
· 使用定理 `Submodule.span_eq_span`：span_eq_span (hs : s subseteq span R t) (ht : t 
subseteq span R s) : span R s = span R t
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Algebra.linearMap_apply`：linearMap_apply (r : R) : Algebra.linearMap R A
 r = algebraMap R A r
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `FractionalIdeal.mem_coeIdeal_of_mem`：mem_coeIdeal_of_mem {x : R} {I : Id
eal R} (hx : x in I) : algebraMap R P x in (I : FractionalIdeal S P)
-/
theorem extended_coeIdeal_eq_map (I₀ : Ideal A) :
    (I₀ : FractionalIdeal M K).extended L hf = (I₀.map f : FractionalIdeal N L) := by
  rw [Ideal.map, Ideal.span, ← coeToSubmodule_inj, Ideal.submodule_span_eq, coe_coeIdeal,
    IsLocalization.coeSubmodule_span, coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨f a, Set.mem_image_of_mem f ha, by rw [Algebra.linearMap_apply, IsLocalization.map_eq hf a]⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨algebraMap A K a, mem_coeIdeal_of_mem M ha, IsLocalization.map_eq hf a⟩

/-- The extension of a principal fractional ideal is the principal ideal generated by the extension
of a generator. -/
/-
**FractionalIdeal.extended_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `FractionalId
eal`。
形式化陈述：extended_spanSingleton (x : K) : (spanSingleton M x).extended L hf = spanS
ingleton N (IsLocalization.map L f hf x)
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `FractionalIdeal.ext`：ext {I J : FractionalIdeal S P} : (forall x, x in I
 ↔ x in J) -> I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.mem_extended_iff`：mem_extended_iff (x : L) : x in I.exte
nded L hf ↔ x in span B (map_f '' I)
· 使用定理 `FractionalIdeal.mem_spanSingleton`：mem_spanSingleton {x y : P} : x in sp
anSingleton S y ↔ exists z : R, z • y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `FractionalIdeal.mem_spanSingleton_self`：mem_spanSingleton_self (x : P) :
 x in spanSingleton S x

--- 原说明 ---
The extension of a principal fractional ideal is the principal ideal generated b
y the extension
of a generator.
-/
theorem extended_spanSingleton (x : K) :
    (spanSingleton M x).extended L hf = spanSingleton N (IsLocalization.map L f hf x) := by
  ext
  rw [mem_extended_iff, mem_spanSingleton, ← mem_span_singleton]
  refine ⟨fun hy ↦ span_le.2 ?_ hy, fun hy ↦ span_le.2 (fun _ h ↦ ?_) hy⟩
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_spanSingleton _).1 hw
    rw [SetLike.mem_coe, Algebra.smul_def, map_mul, IsLocalization.map_eq, ← Algebra.smul_def]
    exact smul_mem _ _ (mem_span_singleton_self _)
  · exact subset_span ⟨x, SetLike.mem_coe.mpr (mem_spanSingleton_self _ x), h.symm⟩

/--
The ring homomorphism version of `FractionalIdeal.extended`.
See `FractionalIdeal.extendedHom` for a more convenient version that is often enough.
-/
@[simps]
/-
**FractionalIdeal.extendedHom'** 是 Mathlib 中的一个定义，位于命名空间 `FractionalIdeal`。
形式化陈述：extendedHom' : FractionalIdeal M K ->+* FractionalIdeal N L where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.extended_one`：extended_one : extended L hf (1 : Fraction
alIdeal M K) = 1
· 使用定理 `FractionalIdeal.extended_mul`：extended_mul : (I * J).extended L hf = (I.
extended L hf) * (J.extended L hf)
· 使用定理 `FractionalIdeal.extended_zero`：extended_zero : extended L hf (0 : Fracti
onalIdeal M K) = 0
· 使用定理 `FractionalIdeal.extended_add`：extended_add : (I + J).extended L hf = (I.
extended L hf) + (J.extended L hf)

--- 原说明 ---
The ring homomorphism version of `FractionalIdeal.extended`.
See `FractionalIdeal.extendedHom` for a more convenient version that is often en
ough.
-/
def extendedHom' : FractionalIdeal M K →+* FractionalIdeal N L where
  toFun := extended L hf
  map_one' := extended_one L hf
  map_zero' := extended_zero L hf
  map_mul' := extended_mul L hf
  map_add' := extended_add L hf

/-- The homomorphisms induced by extension of fractional ideals compose in towers. -/
/-
**FractionalIdeal.extendedHom'_comp** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {B : Type u_2} [inst_1 : CommRing B] 
{f : A →+* B} {K : Type u_3} {M : Submonoid A}   [inst_2 : CommRing K] [inst_3 :
 Algebra A K] [inst_4 : IsLocalization M K] (L : Type u_4) {N : Submonoid B}   [
inst_5 : CommRing L] [inst_6 : Algebra B L] [inst_7 : IsLocalization N L] (hf : 
M ≤ Submonoid.comap f N)   {C : Type u_5} {W : Type u_6} [inst_8 : CommRing C] [
inst_9 : CommRing W] [inst_10 : Algebra C W] {P : Submonoid C}   [inst_11 : IsLo
calization P W] {g : B →+* C} (hg : N ≤ Submonoid.comap g P),   (FractionalIdeal
.extendedHom' W hg).comp (FractionalIdeal.extendedHom' L hf) = FractionalIdeal.e
xtendedHom' W ⋯
参数：L : Type u_4；hf : M ≤ Submonoid.comap f N；hg : N ≤ Submonoid.comap g P；Fracti
onalIdeal.extendedHom' W hg；FractionalIdeal.extendedHom' L hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submonoid.monotone_comap`：monotone_comap {f : F} : Monotone (comap f)
· 使用定理 `FractionalIdeal.extended_extended`：extended_extended {C W : Type*} [Comm
Ring C] [CommRing W] [Algebra C W] {P : Submonoid C} [IsLocalization P W] {g : B
 ->+* C} (hg : N <= Sub…

--- 原说明 ---
The homomorphisms induced by extension of fractional ideals compose in towers.
-/
theorem extendedHom'_comp {C W : Type*} [CommRing C] [CommRing W] [Algebra C W]
    {P : Submonoid C} [IsLocalization P W] {g : B →+* C} (hg : N ≤ Submonoid.comap g P) :
    (extendedHom' (A := B) (K := L) W hg).comp
      (extendedHom' (A := A) (K := K) L hf) =
        extendedHom' (A := A) (B := C) (f := g.comp f) (K := K) W
          (hf.trans (Submonoid.monotone_comap (f := f) hg)) := by
  apply RingHom.ext
  intro I
  exact extended_extended (A := A) (B := B) (f := f) (K := K) (M := M) (L := L)
    (N := N) (hf := hf) (I := I) (C := C) (W := W) (P := P) (g := g) hg

end RingHom

section Algebra

open scoped nonZeroDivisors

variable {A K : Type*} (L B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [IsTorsionFree A B] [Field K] [Field L] [Algebra A K] [Algebra B L]
  [IsFractionRing A K] [IsFractionRing B L] {I : FractionalIdeal A⁰ K}

/--
The ring homomorphism that extends a fractional ideal of `A` to a fractional ideal of `B` for
an extension of domains `A ⊆ B`.
-/
/-
**FractionalIdeal.extendedHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `FractionalIdeal`。
形式化陈述：extendedHom : FractionalIdeal A⁰ K ->+* FractionalIdeal B⁰ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism that extends a fractional ideal of `A` to a fractional ide
al of `B` for
an extension of domains `A ⊆ B`.
-/
abbrev extendedHom : FractionalIdeal A⁰ K →+* FractionalIdeal B⁰ L :=
  extendedHom' L <|
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

@[deprecated (since := "2026-04-16")] alias extendedHomₐ := extendedHom
/-
**FractionalIdeal.extendedHom_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
形式化陈述：extendedHom_eq_zero_iff {I : FractionalIdeal A⁰ K} : extendedHom L B I = 0
 ↔ I = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.extended_eq_zero_iff`：extended_eq_zero_iff [IsDomain B] 
(hf' : Function.Injective f) (hN : 0 ∉ N) : extended L hf I = 0 ↔ I = 0
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `zero_notMem_nonZeroDivisors`：zero_notMem_nonZeroDivisors : 0 ∉ M₀⁰
-/
theorem extendedHom_eq_zero_iff {I : FractionalIdeal A⁰ K} :
    extendedHom L B I = 0 ↔ I = 0 :=
  extended_eq_zero_iff _ _ (FaithfulSMul.algebraMap_injective _ _) zero_notMem_nonZeroDivisors

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_eq_zero_iff := extendedHom_eq_zero_iff
/-
**FractionalIdeal.extendedHom_coeIdeal_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Fractio
nalIdeal`。
形式化陈述：extendedHom_coeIdeal_eq_map (I : Ideal A) : (I : FractionalIdeal A⁰ K).ext
endedHom L B = (I.map (algebraMap A B) : FractionalIdeal B⁰ L)
参数：I : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.extended_coeIdeal_eq_map`：extended_coeIdeal_eq_map (I₀ :
 Ideal A) : (I₀ : FractionalIdeal M K).extended L hf = (I₀.map f : FractionalIde
al N L)
-/
theorem extendedHom_coeIdeal_eq_map (I : Ideal A) :
    (I : FractionalIdeal A⁰ K).extendedHom L B =
      (I.map (algebraMap A B) : FractionalIdeal B⁰ L) := extended_coeIdeal_eq_map L _ I

@[deprecated (since := "2026-04-16")]
alias extendedHomₐ_coeIdeal_eq_map := extendedHom_coeIdeal_eq_map
/-
**FractionalIdeal.extendedHom_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Fractiona
lIdeal`。
形式化陈述：extendedHom_spanSingleton (x : K) : extendedHom L B (spanSingleton A⁰ x) =
 spanSingleton B⁰ (IsFractionRing.map (FaithfulSMul.algebraMap_injective A B) x)
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.extended_spanSingleton`：extended_spanSingleton (x : K) :
 (spanSingleton M x).extended L hf = spanSingleton N (IsLocalization.map L f hf 
x)
-/
theorem extendedHom_spanSingleton (x : K) : extendedHom L B (spanSingleton A⁰ x) =
    spanSingleton B⁰ (IsFractionRing.map (FaithfulSMul.algebraMap_injective A B) x) :=
  extended_spanSingleton L _ x

variable [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsIntegral A B]
/-
**FractionalIdeal.coe_extendedHom_eq_span** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
形式化陈述：coe_extendedHom_eq_span (I : FractionalIdeal A⁰ K) : extendedHom L B I = s
pan B (algebraMap K L '' I)
参数：I : FractionalIdeal A⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.extendedHom'_apply`：∀ {A : Type u_1} [inst : CommRing A]
 {B : Type u_2} [inst_1 : CommRing B] {f : A →+* B} {K : Type u_3} {M : Submonoi
d A}   [inst_2 : CommRin…
· 使用引理 `FractionalIdeal.coe_extended_eq_span`：coe_extended_eq_span : I.extended 
L hf = span B (map_f '' I)
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors
`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `IsLocalization.algebraMap_eq_map_map_submonoid`：IsLocalization.algebraMa
p_eq_map_map_submonoid : algebraMap Rₘ Sₘ = map Sₘ (algebraMap R S) (show _ <= (
Algebra.algebraMapSubmonoid S M).com…
-/
theorem coe_extendedHom_eq_span (I : FractionalIdeal A⁰ K) :
    extendedHom L B I = span B (algebraMap K L '' I) := by
  rw [extendedHom'_apply, coe_extended_eq_span,
    IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
  rfl

@[deprecated (since := "2026-04-16")] alias coe_extendedHomₐ_eq_span := coe_extendedHom_eq_span
/-
**FractionalIdeal.le_one_of_extendedHom_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Fracti
onalIdeal`。
形式化陈述：le_one_of_extendedHom_le_one [IsIntegrallyClosed A] [IsIntegrallyClosed B]
 (hI : extendedHom L B I <= 1) : I <= 1
参数：hI : extendedHom L B I <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.not_le_iff_exists`：not_le_iff_exists : ¬p <= q ↔ exists x in p, 
x ∉ q
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors
`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FractionalIdeal.extendedHom'_apply`：∀ {A : Type u_1} [inst : CommRing A]
 {B : Type u_2} [inst_1 : CommRing B] {f : A →+* B} {K : Type u_3} {M : Submonoi
d A}   [inst_2 : CommRin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.algebraMap_eq_map_map_submonoid`：IsLocalization.algebraMa
p_eq_map_map_submonoid : algebraMap Rₘ Sₘ = map Sₘ (algebraMap R S) (show _ <= (
Algebra.algebraMapSubmonoid S M).com…
· 使用引理 `FractionalIdeal.coe_extended_eq_span`：coe_extended_eq_span : I.extended 
L hf = span B (map_f '' I)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsIntegrallyClosed.isIntegral_iff`：isIntegral_iff [IsIntegrallyClosed R]
 {x : K} : IsIntegral R x ↔ exists y : R, algebraMap R K y = x
· 使用定理 `IsIntegral.tower_bot_of_field`：IsIntegral.tower_bot_of_field {R A B : Ty
pe*} [CommRing R] [Field A] [Ring B] [Nontrivial B] [Algebra R A] [Algebra A B] 
[Algebra R B] [IsSc…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
-/
theorem le_one_of_extendedHom_le_one [IsIntegrallyClosed A] [IsIntegrallyClosed B]
    (hI : extendedHom L B I ≤ 1) : I ≤ 1 := by
  contrapose hI
  rw [SetLike.not_le_iff_exists] at hI ⊢
  obtain ⟨x, hx₁, hx₂⟩ := hI
  refine ⟨algebraMap K L x, ?_, ?_⟩
  · simpa [← FractionalIdeal.mem_coe, IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
      using! subset_span <| Set.mem_image_of_mem _ hx₁
  · contrapose hx₂
    rw [mem_one_iff, ← IsIntegrallyClosed.isIntegral_iff] at hx₂ ⊢
    exact IsIntegral.tower_bot_of_field <| isIntegral_trans _ hx₂

@[deprecated (since := "2026-04-16")]
alias le_one_of_extendedHomₐ_le_one := le_one_of_extendedHom_le_one
/-
**FractionalIdeal.extendedHom_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalId
eal`。
形式化陈述：extendedHom_le_one_iff [IsIntegrallyClosed A] [IsIntegrallyClosed B] : ext
endedHom L B I <= 1 ↔ I <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.le_one_of_extendedHom_le_one`：le_one_of_extendedHom_le_o
ne [IsIntegrallyClosed A] [IsIntegrallyClosed B] (hI : extendedHom L B I <= 1) :
 I <= 1
· 使用定理 `FractionalIdeal.extended_le_one_of_le_one`：extended_le_one_of_le_one (hI
 : I <= 1) : extended L hf I <= 1
-/
theorem extendedHom_le_one_iff [IsIntegrallyClosed A] [IsIntegrallyClosed B] :
    extendedHom L B I ≤ 1 ↔ I ≤ 1 :=
  ⟨fun h ↦ le_one_of_extendedHom_le_one L B h, fun a ↦ extended_le_one_of_le_one L _ I a⟩

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_le_one_iff := extendedHom_le_one_iff

section IsDedekindDomain

set_option linter.overlappingInstances false

variable [IsDedekindDomain A] [IsDedekindDomain B]

/-
**FractionalIdeal.one_le_extendedHom_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalId
eal`。
形式化陈述：one_le_extendedHom_iff (hI : I != 0) : 1 <= extendedHom L B I ↔ 1 <= I
参数：hI : I != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.inv_le_inv_iff`：inv_le_inv_iff {I J : FractionalIdeal A⁰
 K} (hI : I != 0) (hJ : J != 0) : I⁻¹ <= J⁻¹ ↔ J <= I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `FractionalIdeal.extendedHom_eq_zero_iff`：extendedHom_eq_zero_iff {I : Fr
actionalIdeal A⁰ K} : extendedHom L B I = 0 ↔ I = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `FractionalIdeal.extendedHom_le_one_iff`：extendedHom_le_one_iff [IsIntegr
allyClosed A] [IsIntegrallyClosed B] : extendedHom L B I <= 1 ↔ I <= 1
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用引理 `FractionalIdeal.inv_le_comm`：inv_le_comm {I J : FractionalIdeal A⁰ K} (h
I : I != 0) (hJ : J != 0) : I⁻¹ <= J ↔ J⁻¹ <= I
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le_extendedHom_iff (hI : I ≠ 0) : 1 ≤ extendedHom L B I ↔ 1 ≤ I := by
  rw [← inv_le_inv_iff ((extendedHom_eq_zero_iff _ _).not.mpr hI) (by simp), inv_one, ← map_inv₀,
    extendedHom_le_one_iff, inv_le_comm hI (by simp), inv_one]

@[deprecated (since := "2026-04-16")] alias one_le_extendedHomₐ_iff := one_le_extendedHom_iff
/-
**FractionalIdeal.extendedHom_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalId
eal`。
形式化陈述：extendedHom_eq_one_iff (hI : I != 0) : extendedHom L B I = 1 ↔ I = 1
参数：hI : I != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `FractionalIdeal.extendedHom_le_one_iff`：extendedHom_le_one_iff [IsIntegr
allyClosed A] [IsIntegrallyClosed B] : extendedHom L B I <= 1 ↔ I <= 1
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `FractionalIdeal.one_le_extendedHom_iff`：one_le_extendedHom_iff (hI : I !
= 0) : 1 <= extendedHom L B I ↔ 1 <= I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem extendedHom_eq_one_iff (hI : I ≠ 0) : extendedHom L B I = 1 ↔ I = 1 := by
  rw [le_antisymm_iff, extendedHom_le_one_iff, one_le_extendedHom_iff _ _ hI, ← le_antisymm_iff]

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_eq_one_iff := extendedHom_eq_one_iff

variable (A K) in
/-
**FractionalIdeal.extendedHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：extendedHom_injective : Function.Injective (fun I : FractionalIdeal A⁰ K =
> extendedHom L B I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `FractionalIdeal.extendedHom_eq_zero_iff`：extendedHom_eq_zero_iff {I : Fr
actionalIdeal A⁰ K} : extendedHom L B I = 0 ↔ I = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `mul_inv_eq_one₀`：mul_inv_eq_one₀ (hb : b != 0) : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `FractionalIdeal.extendedHom_eq_one_iff`：extendedHom_eq_one_iff (hI : I !
= 0) : extendedHom L B I = 1 ↔ I = 1
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
theorem extendedHom_injective :
    Function.Injective (fun I : FractionalIdeal A⁰ K ↦ extendedHom L B I) := by
  intro I J h
  dsimp only at h
  by_cases hI : I = 0
  · rwa [hI, map_zero, eq_comm, extendedHom_eq_zero_iff L B, eq_comm, ← hI] at h
  by_cases hJ : J = 0
  · rwa [hJ, map_zero, extendedHom_eq_zero_iff L B, ← hJ] at h
  rwa [← mul_inv_eq_one₀ ((extendedHom_eq_zero_iff _ _).not.mpr hJ), ← map_inv₀, ← map_mul,
    extendedHom_eq_one_iff _ _ (mul_ne_zero hI (inv_ne_zero hJ)), mul_inv_eq_one₀ hJ] at h

@[deprecated (since := "2026-04-16")] alias extendedHomₐ_injective := extendedHom_injective

end IsDedekindDomain

end Algebra

end FractionalIdeal

