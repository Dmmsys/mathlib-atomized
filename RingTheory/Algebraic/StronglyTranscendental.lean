/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Strongly transcendental elements

In this file, we provide basic properties for strongly transcendental elements in an algebra.
This is a relatively niche notion, but is useful for proving Zariski's main theorem.

## Reference
- https://stacks.math.columbia.edu/tag/00PZ

-/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

open Polynomial

variable {R S T : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

variable (R) in
/-- We say that `x : S` is strongly transcendental over `R` if
forall `u : S` and all `p : R[X]`, `p(x) * u = 0 → p * u = 0`.
If `S` is a domain, and `R ⊆ S`, this is equivalent to the image of `x` in `Frac(S)` being
transcendental over `R`. See `IsStronglyTranscendental.iff_of_isFractionRing`.
-/
@[stacks 00PZ]
/-
**IsStronglyTranscendental** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsStronglyTranscendental (x : S) : Prop
参数：x : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `x : S` is strongly transcendental over `R` if
forall `u : S` and all `p : R[X]`, `p(x) * u = 0 → p * u = 0`.
If `S` is a domain, and `R ⊆ S`, this is equivalent to the image of `x` in `Frac
(S)` being
transcendental over `R`. See `IsStronglyTranscendental.iff_of_isFractionRing`.
-/
def IsStronglyTranscendental (x : S) : Prop :=
  ∀ u : S, ∀ p : R[X], p.aeval x * u = 0 → p.map (algebraMap R S) * C u = 0
/-
**IsStronglyTranscendental.transcendental** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStronglyTranscendental.transcendental {x : S} (h : IsStronglyTranscenden
tal R x) [FaithfulSMul R S] : Transcendental R x
参数：h : IsStronglyTranscendental R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `transcendental_iff`：transcendental_iff {x : A} : Transcendental R x ↔ fo
rall p : R[X], aeval x p = 0 -> p = 0
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma IsStronglyTranscendental.transcendental {x : S} (h : IsStronglyTranscendental R x)
    [FaithfulSMul R S] : Transcendental R x :=
  transcendental_iff.mpr fun p hp ↦ Polynomial.ext <|
    by simpa [Algebra.smul_def, hp, Polynomial.ext_iff] using h 1 p
/-
**isStronglyTranscendental_iff_of_field** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isStronglyTranscendental_iff_of_field {K : Type*} [Field K] [Algebra R K] 
[FaithfulSMul R K] {x : K} : IsStronglyTranscendental R x ↔ Transcendental R x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsStronglyTranscendental.transcendental`：IsStronglyTranscendental.transc
endental {x : S} (h : IsStronglyTranscendental R x) [FaithfulSMul R S] : Transce
ndental R x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
lemma isStronglyTranscendental_iff_of_field {K : Type*} [Field K] [Algebra R K] [FaithfulSMul R K]
    {x : K} : IsStronglyTranscendental R x ↔ Transcendental R x := by
  refine ⟨fun h ↦ h.transcendental, fun h ↦ ?_⟩
  simpa [IsStronglyTranscendental, or_imp, forall_and, @forall_comm K, ← subsingleton_iff_forall_eq,
    not_subsingleton, ext_iff, forall_or_left, ← imp_iff_or_not, transcendental_iff] using h
/-
**IsStronglyTranscendental.of_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStronglyTranscendental.of_map {x : S} {f : S ->ₐ[R] T} (hf : Function.In
jective f) (h : IsStronglyTranscendental R (f x)) : IsStronglyTranscendental R x
参数：hf : Function.Injective f；h : IsStronglyTranscendental R (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `Polynomial.coe_mapRingHom`：coe_mapRingHom (f : R ->+* S) : ⇑(mapRingHom 
f) = map f
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
-/
lemma IsStronglyTranscendental.of_map {x : S} {f : S →ₐ[R] T} (hf : Function.Injective f)
    (h : IsStronglyTranscendental R (f x)) :
    IsStronglyTranscendental R x := by
  intro u p hp
  have := h (f u) p (by rw [aeval_algHom_apply, ← map_mul, hp, map_zero])
  rwa [← f.comp_algebraMap, ← map_map, ← f.coe_toRingHom, ← map_C, ← Polynomial.map_mul,
    ← coe_mapRingHom, map_eq_zero_iff] at this
  exact map_injective f.toRingHom hf
/-
**IsStronglyTranscendental.of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStronglyTranscendental.of_isLocalization [Algebra S T] (M : Submonoid S)
 [IsLocalization M T] [IsScalarTower R S T] {x : S} (h : IsStronglyTranscendenta
l R x) : IsStronglyTranscendental R (algebraMap S T x)
参数：M : Submonoid S；h : IsStronglyTranscendental R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `IsLocalization.smul_mk'`：smul_mk' (x y : R) (m : M) : x • mk' S y m = mk
' S (x * y) m
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 64 条，此处仅展示前 30 条）
-/
lemma IsStronglyTranscendental.of_isLocalization [Algebra S T] (M : Submonoid S)
    [IsLocalization M T] [IsScalarTower R S T]
    {x : S} (h : IsStronglyTranscendental R x) :
    IsStronglyTranscendental R (algebraMap S T x) := by
  intro u p hp
  obtain ⟨u, s, rfl⟩ := IsLocalization.exists_mk'_eq M u
  obtain ⟨a, haM, e⟩ : ∃ a ∈ M, a * ((aeval x) p * u) = 0 := by
    simpa [aeval_algebraMap_apply, ← Algebra.smul_def, IsLocalization.smul_mk',
      IsLocalization.mk'_eq_zero_iff] using hp
  have : p.map (algebraMap R T) * C (a • algebraMap S T u) = 0 := by
    simpa [map_map, ← IsScalarTower.algebraMap_eq, Algebra.smul_def] using
      congr(map (algebraMap S T) $(h (a * u) p (by linear_combination e)))
  refine ((IsLocalization.map_units T (⟨a, haM⟩ * s)).map C).mul_right_cancel ?_
  simpa [mul_assoc, ← map_mul, mul_comm _ (algebraMap _ _ _), ← Algebra.smul_def, mul_smul]
/-
**IsStronglyTranscendental.of_isLocalization_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStronglyTranscendental.of_isLocalization_left [Algebra S T] (M : Submono
id R) [IsLocalization M S] [IsScalarTower R S T] {x : T} (h : IsStronglyTranscen
dental R x) : IsStronglyTranscendental S x
参数：M : Submonoid R；h : IsStronglyTranscendental R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.integerNormalization_spec`：integerNormalization_spec (p :
 S[X]) : exists b in M, (integerNormalization M p).map (algebraMap R S) = b • p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `AlgHom.map_smul_of_tower`：map_smul_of_tower {R'} [SMul R' A] [SMul R' B]
 [LinearMap.CompatibleSMul A B R' R] (r : R') (x : A) : φ (r • x) = r • φ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
-/
lemma IsStronglyTranscendental.of_isLocalization_left [Algebra S T] (M : Submonoid R)
    [IsLocalization M S] [IsScalarTower R S T]
    {x : T} (h : IsStronglyTranscendental R x) :
    IsStronglyTranscendental S x := by
  intro t p hp
  obtain ⟨a, ha₁, ha₂⟩ := IsLocalization.integerNormalization_spec M p
  have H : aeval x (IsLocalization.integerNormalization M p) = a • aeval x p := by
    simpa [AlgHom.map_smul_of_tower] using congr(aeval x $ha₂)
  have := h t (IsLocalization.integerNormalization M p) (by simp [H, hp])
  rw [IsScalarTower.algebraMap_eq R S T, ← map_map, ha₂] at this
  rw [← (((IsLocalization.map_units S ⟨a, ha₁⟩).map (algebraMap S T)).map C).mul_right_inj]
  simpa [Algebra.smul_def, mul_assoc] using this
/-
**IsStronglyTranscendental.restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStronglyTranscendental.restrictScalars [Algebra S T] [IsScalarTower R S 
T] {x : T} (h : IsStronglyTranscendental S x) : IsStronglyTranscendental R x
参数：h : IsStronglyTranscendental S x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
-/
lemma IsStronglyTranscendental.restrictScalars [Algebra S T] [IsScalarTower R S T]
    {x : T} (h : IsStronglyTranscendental S x) :
    IsStronglyTranscendental R x := by
  intro t p hp
  simpa [map_map, ← IsScalarTower.algebraMap_eq] using h t (p.map (algebraMap R S)) (by simpa)
/-
**IsStronglyTranscendental.of_surjective_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStronglyTranscendental.of_surjective_left [Algebra S T] [IsScalarTower R
 S T] {x : T} (h : IsStronglyTranscendental R x) (H : Function.Surjective (algeb
raMap R S)) : IsStronglyTranscendental S x
参数：h : IsStronglyTranscendental R x；H : Function.Surjective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
-/
lemma IsStronglyTranscendental.of_surjective_left [Algebra S T] [IsScalarTower R S T]
    {x : T} (h : IsStronglyTranscendental R x) (H : Function.Surjective (algebraMap R S)) :
    IsStronglyTranscendental S x := by
  intro t p hp
  obtain ⟨p, rfl⟩ := map_surjective _ H p
  simpa [map_map, ← IsScalarTower.algebraMap_eq] using h t p (by simpa using hp)
/-
**IsStronglyTranscendental.iff_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStronglyTranscendental.iff_of_isLocalization [Algebra S T] {M : Submonoi
d S} (hM : M <= S⁰) [IsLocalization M T] [IsScalarTower R S T] {x : S} : IsStron
glyTranscendental R (algebraMap S T x) ↔ IsStronglyTranscendental R x
参数：hM : M <= S⁰。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsStronglyTranscendental.of_map`：IsStronglyTranscendental.of_map {x : S}
 {f : S ->ₐ[R] T} (hf : Function.Injective f) (h : IsStronglyTranscendental R (f
 x)) : IsStronglyTran…
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用引理 `IsStronglyTranscendental.of_isLocalization`：IsStronglyTranscendental.of_
isLocalization [Algebra S T] (M : Submonoid S) [IsLocalization M T] [IsScalarTow
er R S T] {x : S} (h : IsStrongl…
-/
lemma IsStronglyTranscendental.iff_of_isLocalization [Algebra S T] {M : Submonoid S}
    (hM : M ≤ S⁰) [IsLocalization M T] [IsScalarTower R S T]
    {x : S} : IsStronglyTranscendental R (algebraMap S T x) ↔ IsStronglyTranscendental R x :=
  ⟨fun h ↦ .of_map (f := IsScalarTower.toAlgHom R S T) (IsLocalization.injective _ hM) h,
    fun h ↦ .of_isLocalization M h⟩
/-
**IsStronglyTranscendental.iff_of_isFractionRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStronglyTranscendental.iff_of_isFractionRing (K : Type*) [Field K] [Alge
bra R K] [Algebra S K] [IsScalarTower R S K] [FaithfulSMul R S] [IsFractionRing 
S K] {x : S} : IsStronglyTranscendental R x ↔ Transcendental R (algebraMap S K x
)
参数：K : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.trans`：FaithfulSMul.trans (R S T : Type*) [Monoid S] [MulOn
eClass T] [SMul R S] [IsScalarTower R S S] [MulAction S T] [IsScalarTower S T T]
 [SMul R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsStronglyTranscendental.iff_of_isLocalization`：IsStronglyTranscendental
.iff_of_isLocalization [Algebra S T] {M : Submonoid S} (hM : M <= S⁰) [IsLocaliz
ation M T] [IsScalarTower R S T] {x …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `isStronglyTranscendental_iff_of_field`：isStronglyTranscendental_iff_of_f
ield {K : Type*} [Field K] [Algebra R K] [FaithfulSMul R K] {x : K} : IsStrongly
Transcendental R x ↔ Transc…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsStronglyTranscendental.iff_of_isFractionRing (K : Type*) [Field K] [Algebra R K]
    [Algebra S K] [IsScalarTower R S K] [FaithfulSMul R S] [IsFractionRing S K] {x : S} :
    IsStronglyTranscendental R x ↔ Transcendental R (algebraMap S K x) := by
  have : FaithfulSMul R K := .trans R S K
  rw [← IsStronglyTranscendental.iff_of_isLocalization (T := K) le_rfl,
    isStronglyTranscendental_iff_of_field]
/-
**IsStronglyTranscendental.of_transcendental** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStronglyTranscendental.of_transcendental {K : Type*} [Field K] [Algebra 
R K] [Algebra S K] [IsScalarTower R S K] [FaithfulSMul R S] [FaithfulSMul S K] {
x : S} (H : Transcendental R (algebraMap S K x)) : IsStronglyTranscendental R x
参数：H : Transcendental R (algebraMap S K x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.trans`：FaithfulSMul.trans (R S T : Type*) [Monoid S] [MulOn
eClass T] [SMul R S] [IsScalarTower R S S] [MulAction S T] [IsScalarTower S T T]
 [SMul R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsStronglyTranscendental.of_map`：IsStronglyTranscendental.of_map {x : S}
 {f : S ->ₐ[R] T} (hf : Function.Injective f) (h : IsStronglyTranscendental R (f
 x)) : IsStronglyTran…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isStronglyTranscendental_iff_of_field`：isStronglyTranscendental_iff_of_f
ield {K : Type*} [Field K] [Algebra R K] [FaithfulSMul R K] {x : K} : IsStrongly
Transcendental R x ↔ Transc…
-/
lemma IsStronglyTranscendental.of_transcendental {K : Type*} [Field K] [Algebra R K]
    [Algebra S K] [IsScalarTower R S K] [FaithfulSMul R S] [FaithfulSMul S K]
    {x : S} (H : Transcendental R (algebraMap S K x)) :
    IsStronglyTranscendental R x := by
  have : FaithfulSMul R K := .trans R S K
  rw [← isStronglyTranscendental_iff_of_field] at H
  exact .of_map (f := IsScalarTower.toAlgHom R S K) (FaithfulSMul.algebraMap_injective _ _) H

@[stacks 00Q0]
/-
**isStronglyTranscendental_mk_of_mem_minimalPrimes** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isStronglyTranscendental_mk_of_mem_minimalPrimes [IsReduced S] {x : S} (hx
 : IsStronglyTranscendental R x) (q : Ideal S) (hq : q in minimalPrimes S) : IsS
tronglyTranscendental R (Ideal.Quotient.mk q x)
参数：hx : IsStronglyTranscendental R x；q : Ideal S；hq : q in minimalPrimes S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Ring.KrullDimLE.of_isLocalization`：Ring.KrullDimLE.of_isLocalization (p 
: Ideal R) (hp : p in minimalPrimes R) (S : Type*) [CommSemiring S] [Algebra R S
] [IsLocalization.AtPri…
· 使用引理 `Ring.KrullDimLE.isField_of_isReduced`：Ring.KrullDimLE.isField_of_isReduc
ed [IsReduced R] [IsLocalRing R] : IsField R
· 使用定理 `instIsReducedLocalization`：∀ {R : Type u_1} [inst : CommRing R] (M : Sub
monoid R) [IsReduced R], IsReduced (Localization M)
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsLocalRing.maximalIdeal_eq_bot`：maximalIdeal_eq_bot {R : Type*} [Field 
R] : IsLocalRing.maximalIdeal R = ⊥
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Ideal.Quotient.algebraMap_eq`：∀ {R : Type u_5} [inst : CommRing R] (I : 
Ideal R), algebraMap R (R ⧸ I) = Ideal.Quotient.mk I
· 使用定理 `Polynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : A) (p : R
[X]) : aeval (algebraMap A B x) p = algebraMap A B (aeval x p)
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a
（共 67 条，此处仅展示前 30 条）
-/
lemma isStronglyTranscendental_mk_of_mem_minimalPrimes [IsReduced S]
    {x : S} (hx : IsStronglyTranscendental R x) (q : Ideal S) (hq : q ∈ minimalPrimes S) :
    IsStronglyTranscendental R (Ideal.Quotient.mk q x) := by
  refine Ideal.Quotient.mk_surjective.forall.mpr fun u p e ↦ ?_
  rw [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at e
  have := hq.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime q) := .of_isLocalization _ hq _
  let : Field (Localization.AtPrime q) := Ring.KrullDimLE.isField_of_isReduced.toField
  obtain ⟨⟨m, hmq⟩, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q)
    (aeval x p * u)).mp (by rw [← Ideal.mem_bot, ← IsLocalRing.maximalIdeal_eq_bot,
      ← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ e)
  ext i
  simp only [coeff_mul_C, coeff_map, coeff_zero, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  have : algebraMap R S (p.coeff i) * u * m = 0 := by
    simpa [← mul_assoc] using congr(($(hx (u * m) p (by linear_combination hm))).coeff i)
  exact (Ideal.IsPrime.mem_or_mem_of_mul_eq_zero ‹_› (by linear_combination this)).resolve_left hmq
