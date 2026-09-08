/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-!
# The finite adèle ring of a Dedekind domain

We define the ring of finite adèles of a Dedekind domain `R`.

## Main definitions
- `IsDedekindDomain.FiniteAdeleRing` : The finite adèle ring of `R`, defined as the
  restricted product `Πʳ_v K_v`. We give this ring a `K`-algebra structure.

## Implementation notes
We are only interested on Dedekind domains of Krull dimension 1 (i.e., not fields). If `R` is a
field, its finite adèle ring is just defined to be the trivial ring.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite adèle ring, dedekind domain
-/

@[expose] public section

variable (R : Type*) [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K]

namespace IsDedekindDomain

/--
The support of an element `k` of the field of fractions of a Dedekind domain is
the set of maximal ideals of the Dedekind domain at which `k` is not integral.
-/
/-
**IsDedekindDomain.HeightOneSpectrum.Support** 是 Mathlib 中的一个定义，位于命名空间 `IsDedeki
ndDomain.HeightOneSpectrum`。
形式化陈述：(R : Type u_1) →   [inst : CommRing R] →     [IsDedekindDomain R] →       
{K : Type u_2} →         [inst_2 : Field K] →           [inst_3 : Algebra R K] →
 [IsFractionRing R K] → K → Set (IsDedekindDomain.HeightOneSpectrum R)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of an element `k` of the field of fractions of a Dedekind domain is
the set of maximal ideals of the Dedekind domain at which `k` is not integral.
-/
def HeightOneSpectrum.Support (k : K) : Set (HeightOneSpectrum R) :=
    {v : HeightOneSpectrum R | 1 < v.valuation K k}

/--
The support of an element of the field of fractions of a Dedekind domain
is finite.
-/
/-
**IsDedekindDomain.HeightOneSpectrum.Support.finite** 是 Mathlib 中的一个定理，位于命名空间 `I
sDedekindDomain.HeightOneSpectrum.Support`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDedekindDomain R] {K : Ty
pe u_2} [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (k : K), (IsDedekindDomain.HeightOneSpectrum.Support R k).Finite
参数：R : Type u_1；k : K；IsDedekindDomain.HeightOneSpectrum.Support R k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.finite_factors`：Ideal.finite_factors {I : Ideal R} (hI : I != 0) :
 {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one`：intValuation_le_
one (x : R) : v.intValuation x <= 1
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `lt_mul_of_one_lt_right`：lt_mul_of_one_lt_right [PosMulStrictMono α] (ha 
: 0 < a) (h : 1 < b) : a < a * b
· 使用定理 `instPosMulStrictMonoWithZeroOfMulLeftStrictMono`：∀ {α : Type u_1} [inst 
: Mul α] [inst_1 : Preorder α] [MulLeftStrictMono α], PosMulStrictMono (WithZero
 α)
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The support of an element of the field of fractions of a Dedekind domain
is finite.
-/
lemma HeightOneSpectrum.Support.finite (k : K) : (Support R k).Finite := by
  -- We write k=n/d.
  obtain ⟨⟨n, ⟨d, hd⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
  have hd' : d ≠ 0 := nonZeroDivisors.ne_zero hd
  suffices {v : HeightOneSpectrum R | v.valuation K (algebraMap R K d) < 1}.Finite by
    apply Set.Finite.subset this
    intro v hv
    apply_fun v.valuation K at hk
    simp only [Valuation.map_mul, valuation_of_algebraMap] at hk
    rw [Set.mem_ofPred_eq, valuation_of_algebraMap]
    have := intValuation_le_one v n
    contrapose! this
    rw [← hk, mul_comm]
    exact (lt_mul_of_one_lt_right (by simp) hv).trans_le <|
      mul_le_mul_of_nonneg_right this (by simp)
  simp_rw [valuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]

end IsDedekindDomain

noncomputable section

open Function Set IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

variable (K)

open scoped RestrictedProduct

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adicCompletion` with respect to `adicCompletionIntegers`. We prove that it is a commutative
ring. -/

/--
If `K` is the field of fractions of the Dedekind domain `R` then `FiniteAdeleRing R K` is
the ring of finite adeles of `K`, defined as the restricted product of the completions
`K_v` with respect to the subrings `R_v`. Here `v` runs through the nonzero primes of `R`
and the restricted product is the subring of `∏_v K_v` consisting of elements which
are in `R_v` for all but finitely many `v`.
-/
/-
**IsDedekindDomain.FiniteAdeleRing** 是 Mathlib 中的一个定义，位于命名空间 `IsDedekindDomain`。
形式化陈述：FiniteAdeleRing : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K` is the field of fractions of the Dedekind domain `R` then `FiniteAdeleRin
g R K` is
the ring of finite adeles of `K`, defined as the restricted product of the compl
etions
`K_v` with respect to the subrings `R_v`. Here `v` runs through the nonzero prim
es of `R`
and the restricted product is the subring of `∏_v K_v` consisting of elements wh
ich
are in `R_v` for all but finitely many `v`.
-/
def FiniteAdeleRing : Type _ :=
  Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
/-
**IsDedekindDomain.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (FiniteAdeleRing R K) := inferInstanceAs <|
  CommRing <| Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
/-
**IsDedekindDomain.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (FiniteAdeleRing R K) := inferInstanceAs <|
  TopologicalSpace <| Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]
/-
**IsDedekindDomain.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DFunLike (FiniteAdeleRing R K) (HeightOneSpectrum R) (adicCompletion K) where
  coe a := a.1
  coe_injective _ _ := Subtype.ext

namespace FiniteAdeleRing

/-- `𝔸ᶠ[R, K]` is notation for `IsDedekindDomain.FiniteAdeleRing R K`. -/
scoped notation:max "𝔸ᶠ[" R ", " K "]" => FiniteAdeleRing R K

/--
The canonical map from `K` to the finite adeles of `K`.

The content of the existence of this map is the fact that an element `k` of `K` is integral at
all but finitely many places, which is `IsDedekindDomain.HeightOneSpectrum.Support.finite R k`.
-/
/-
**IsDedekindDomain.FiniteAdeleRing.algebraMap** 是 Mathlib 中的一个定义，位于命名空间 `IsDedek
indDomain.FiniteAdeleRing`。
形式化陈述：(R : Type u_1) →   [inst : CommRing R] →     [inst_1 : IsDedekindDomain R]
 →       (K : Type u_2) →         [inst_2 : Field K] →           [inst_3 : Algeb
ra R K] → [inst_4 : IsFractionRing R K] → K →+* IsDedekindDomain.FiniteAdeleRing
 R K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `K` to the finite adeles of `K`.

The content of the existence of this map is the fact that an element `k` of `K` 
is integral at
all but finitely many places, which is `IsDedekindDomain.HeightOneSpectrum.Suppo
rt.finite R k`.
-/
protected def algebraMap : K →+* 𝔸ᶠ[R, K] where
  toFun k := ⟨fun i ↦ k, by
    simp only [Filter.eventually_cofinite, SetLike.mem_coe, mem_adicCompletionIntegers R K,
     valuedAdicCompletion_eq_valuation', not_le]
    exact HeightOneSpectrum.Support.finite R k⟩
  map_one' := Subtype.ext <| funext fun _ ↦ adicCompletion.coe_one ..
  map_mul' x y := Subtype.ext <| funext fun _ ↦ adicCompletion.coe_mul ..
  map_zero' := Subtype.ext <| funext fun _ ↦ adicCompletion.coe_zero ..
  map_add' x y := Subtype.ext <| funext fun _ ↦ adicCompletion.coe_add ..
/-
**IsDedekindDomain.FiniteAdeleRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomain.
FiniteAdeleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra K 𝔸ᶠ[R, K] := (FiniteAdeleRing.algebraMap R K).toAlgebra

@[simp]
/-
**IsDedekindDomain.FiniteAdeleRing.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `I
sDedekindDomain.FiniteAdeleRing`。
形式化陈述：algebraMap_apply (k : K) (v : HeightOneSpectrum R) : algebraMap K 𝔸ᶠ[R, K]
 k v = k
参数：k : K；v : HeightOneSpectrum R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply (k : K) (v : HeightOneSpectrum R) :
    algebraMap K 𝔸ᶠ[R, K] k v = k := rfl
/-
**IsDedekindDomain.FiniteAdeleRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomain.
FiniteAdeleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R 𝔸ᶠ[R, K] := Algebra.compHom _ (algebraMap R K)
/-
**IsDedekindDomain.FiniteAdeleRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomain.
FiniteAdeleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R K 𝔸ᶠ[R, K] :=
  IsScalarTower.of_algebraMap_eq' rfl

variable {R} in
@[ext]
/-
**IsDedekindDomain.FiniteAdeleRing.ext** 是 Mathlib 中的一个引理，位于命名空间 `IsDedekindDoma
in.FiniteAdeleRing`。
形式化陈述：ext {a₁ a₂ : 𝔸ᶠ[R, K]} (h : forall v, a₁ v = a₂ v) : a₁ = a₂
参数：h : forall v, a₁ v = a₂ v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ext {a₁ a₂ : 𝔸ᶠ[R, K]} (h : ∀ v, a₁ v = a₂ v) : a₁ = a₂ :=
  Subtype.ext <| funext h

section Topology

/-
**IsDedekindDomain.FiniteAdeleRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomain.
FiniteAdeleRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalRing 𝔸ᶠ[R, K] :=
  haveI : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  RestrictedProduct.isTopologicalRing (fun (v : HeightOneSpectrum R) ↦ v.adicCompletion K)

end Topology

section Units

variable {R K}

set_option backward.isDefEq.respectTransparency false in
/-
**IsDedekindDomain.FiniteAdeleRing.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsDedek
indDomain.FiniteAdeleRing`。
形式化陈述：isUnit_iff {a : 𝔸ᶠ[R, K]} : IsUnit a ↔ (forall v, a v != 0) ∧ forallᶠ v in
 Filter.cofinite, Valued.v (a v) = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RestrictedProduct.isUnit_iff`：isUnit_iff {x : Πʳ i, [R i, B i]_[𝓕]} : Is
Unit x ↔ (forall i, IsUnit (x i)) ∧ forallᶠ i in 𝓕, exists (h : x i in B i), IsU
nit (⟨x i, h⟩ : B …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isUnit_iff {a : 𝔸ᶠ[R, K]} :
    IsUnit a ↔ (∀ v, a v ≠ 0) ∧ ∀ᶠ v in Filter.cofinite, Valued.v (a v) = 1 := by
  rw [RestrictedProduct.isUnit_iff]
  simp only [isUnit_iff_ne_zero, adicCompletionIntegers.isUnit_iff_valued_eq_one, exists_prop,
    Filter.eventually_cofinite, not_and_or, Set.ofPred_or]
  simpa using! fun _ _ ↦ a.2
/-
**IsDedekindDomain.FiniteAdeleRing.unitsEquiv_finite_valued_eq_one** 是 Mathlib 中
的一个定理，位于命名空间 `IsDedekindDomain.FiniteAdeleRing`。
形式化陈述：unitsEquiv_finite_valued_eq_one (a : 𝔸ᶠ[R, K]ˣ) : forallᶠ v in Filter.cofi
nite, Valued.v (RestrictedProduct.unitsEquiv _ a v).1 = 1
参数：a : 𝔸ᶠ[R, K]ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_
valued_eq_one`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R
] {K : Type u_2} [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFr…
-/
theorem unitsEquiv_finite_valued_eq_one (a : 𝔸ᶠ[R, K]ˣ) :
    ∀ᶠ v in Filter.cofinite, Valued.v (RestrictedProduct.unitsEquiv _ a v).1 = 1 := by
  filter_upwards [(RestrictedProduct.unitsEquiv _ a).2] using fun _ h ↦
    adicCompletionIntegers.mem_units_iff_valued_eq_one.1 h
/-
**IsDedekindDomain.FiniteAdeleRing.infinite_valued_ne_one_of_not_isUnit** 是 Math
lib 中的一个定理，位于命名空间 `IsDedekindDomain.FiniteAdeleRing`。
形式化陈述：infinite_valued_ne_one_of_not_isUnit {a : 𝔸ᶠ[R, K]} (ha₀ : forall v, a v !
= 0) (ha : ¬IsUnit a) : {v | Valued.v (a v) != 1}.Infinite
参数：ha₀ : forall v, a v != 0；ha : ¬IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.FiniteAdeleRing.isUnit_iff`：isUnit_iff {a : 𝔸ᶠ[R, K]} :
 IsUnit a ↔ (forall v, a v != 0) ∧ forallᶠ v in Filter.cofinite, Valued.v (a v) 
= 1
-/
theorem infinite_valued_ne_one_of_not_isUnit {a : 𝔸ᶠ[R, K]} (ha₀ : ∀ v, a v ≠ 0)
    (ha : ¬IsUnit a) : {v | Valued.v (a v) ≠ 1}.Infinite := by
  contrapose! ha
  rw [isUnit_iff]
  exact ⟨ha₀, ha⟩

variable (R)

variable (K) in
/-- The global embedding of the units of `K` into the units of `FiniteAdeleRing R K`. -/
/-
**IsDedekindDomain.FiniteAdeleRing.unitEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `IsDe
dekindDomain.FiniteAdeleRing`。
形式化陈述：unitEmbedding : Kˣ ->* 𝔸ᶠ[R, K]ˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The global embedding of the units of `K` into the units of `FiniteAdeleRing R K`
.
-/
def unitEmbedding : Kˣ →* 𝔸ᶠ[R, K]ˣ := Units.map (algebraMap K 𝔸ᶠ[R, K])
/-
**IsDedekindDomain.FiniteAdeleRing.unitEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间
 `IsDedekindDomain.FiniteAdeleRing`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] [inst_1 : IsDedekindDomain R] {K : Ty
pe u_2} [inst_2 : Field K]   [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K
] (k : Kˣ),   ↑((IsDedekindDomain.FiniteAdeleRing.unitEmbedding R K) k) = (algeb
raMap K (IsDedekindDomain.FiniteAdeleRing R K)) ↑k
参数：R : Type u_1；k : Kˣ；(IsDedekindDomain.FiniteAdeleRing.unitEmbedding R K) k；al
gebraMap K (IsDedekindDomain.FiniteAdeleRing R K)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem unitEmbedding_apply (k : Kˣ) : unitEmbedding R K k = algebraMap K 𝔸ᶠ[R, K] k := rfl

end Units

end FiniteAdeleRing

end IsDedekindDomain

