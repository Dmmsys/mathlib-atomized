/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Intermediate Fields of Rational Function Fields

Results relating `IntermediateField` and `RatFunc`.
-/

variable {K : Type*} [Field K]

namespace RatFunc

open IntermediateField algebraAdjoinAdjoin Polynomial Algebra

@[expose] public section

variable (f : K⟮X⟯)

/-
**RatFunc.adjoin_X** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：adjoin_X : K⟮(X : K⟮X⟯)⟯ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `IntermediateField.mem_adjoin_simple_iff`：mem_adjoin_simple_iff {α : E} (
x : E) : x in adjoin F {α} ↔ exists r s : F[X], x = aeval α r / aeval α s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RatFunc.aeval_X_left_eq_algebraMap`：aeval_X_left_eq_algebraMap (p : K[X]
) : p.aeval (X : K⟮X⟯) = algebraMap K[X] K⟮X⟯ p
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjoin_X : K⟮(X : K⟮X⟯)⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩
/-
**RatFunc.IntermediateField.adjoin_X** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.Intermed
iateField`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (E : IntermediateField K (RatFunc K)), (
↥E)⟮RatFunc.X⟯ = ⊤
参数：E : IntermediateField K (RatFunc K)；↥E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.restrictScalars_eq_top_iff`：restrictScalars_eq_top_iff
 {L : IntermediateField F E} : L.restrictScalars K = ⊤ ↔ L = ⊤
· 使用定理 `IntermediateField.restrictScalars_adjoin`：restrictScalars_adjoin (K : In
termediateField F E) (S : Set E) : restrictScalars F (adjoin K S) = adjoin F (K 
union S)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `RatFunc.adjoin_X`：adjoin_X : K⟮(X : K⟮X⟯)⟯ = ⊤
· 使用定理 `IntermediateField.adjoin.mono`：∀ (F : Type u_1) [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S T : Set E),   S ⊆ T → Inter
mediateField.adjoin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem IntermediateField.adjoin_X (E : IntermediateField K K⟮X⟯) :
    E⟮(X : K⟮X⟯)⟯ = ⊤ := by
  rw [← restrictScalars_eq_top_iff (K := K), IntermediateField.restrictScalars_adjoin,
    _root_.eq_top_iff]
  exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (adjoin.mono _ _ _ (by simp))

/-- The equivalence between `E⟮X⟯` and `K⟮X⟯` as `E`-algebras. -/
/-
**RatFunc.IntermediateField.adjoinXEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RatFunc.Inte
rmediateField`。
形式化陈述：{K : Type u_1} → [inst : Field K] → (E : IntermediateField K (RatFunc K)) 
→ ↥(↥E)⟮RatFunc.X⟯ ≃ₐ[↥E] RatFunc K
参数：E : IntermediateField K (RatFunc K)；↥E。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RatFunc.IntermediateField.adjoin_X`：∀ {K : Type u_1} [inst : Field K] (E
 : IntermediateField K (RatFunc K)), (↥E)⟮RatFunc.X⟯ = ⊤

--- 原说明 ---
The equivalence between `E⟮X⟯` and `K⟮X⟯` as `E`-algebras.
-/
noncomputable def IntermediateField.adjoinXEquiv (E : IntermediateField K K⟮X⟯) :
    E⟮(X : K⟮X⟯)⟯ ≃ₐ[E] K⟮X⟯ :=
  (equivOfEq (adjoin_X E)).trans topEquiv

/-- The minimal polynomial of `X` over `K⟮f⟯`. It is defined as `f.num - f * f.denom`, viewed
as a polynomial with coefficients in `A`, where `A` is a `K[f]`-algebra. -/
/-
**RatFunc.minpolyX** 是 Mathlib 中的一个缩写定义，位于命名空间 `RatFunc`。
形式化陈述：minpolyX (A : Type*) [CommRing A] [Algebra K A] [Algebra K[f] A] : A[X]
参数：A : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal polynomial of `X` over `K⟮f⟯`. It is defined as `f.num - f * f.denom
`, viewed
as a polynomial with coefficients in `A`, where `A` is a `K[f]`-algebra.
-/
noncomputable abbrev minpolyX (A : Type*) [CommRing A] [Algebra K A] [Algebra K[f] A] : A[X] :=
  f.num.map (algebraMap K A) -
  Polynomial.C (algebraMap K[f] A (⟨f, self_mem_adjoin_singleton K f⟩ : K[f])) *
    f.denom.map (algebraMap K A)
/-
**RatFunc.minpolyX_map** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：minpolyX_map (A : Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjo
in K {f}) A] (B : Type*) [CommRing B] [Algebra K B] [Algebra K[f] B] [Algebra A 
B] [IsScalarTower K A B] [IsScalarTower K[f] A B] : (f.minpolyX A).map (algebraM
ap A B) = f.minpolyX B
参数：A : Type*；Algebra.adjoin K {f}；B : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem minpolyX_map (A : Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjoin K {f}) A]
    (B : Type*) [CommRing B] [Algebra K B] [Algebra K[f] B] [Algebra A B] [IsScalarTower K A B]
    [IsScalarTower K[f] A B] : (f.minpolyX A).map (algebraMap A B) = f.minpolyX B := by
  simp [minpolyX, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

@[simp]
/-
**RatFunc.C_minpolyX** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：C_minpolyX (x : K) : (C x).minpolyX K⟮C x⟯ = 0
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RatFunc.num_C`：num_C (c : K) : num (C c) = Polynomial.C c
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `RatFunc.denom_C`：denom_C (c : K) : denom (C c) = 1
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem C_minpolyX (x : K) : (C x).minpolyX K⟮C x⟯ = 0 := by
  simp [minpolyX, sub_eq_zero, Subtype.ext_iff]
/-
**RatFunc.minpolyX_aeval_X** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：minpolyX_aeval_X : (f.minpolyX K⟮f⟯).aeval (X : K⟮X⟯) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `RatFunc.aeval_X_left_eq_algebraMap`：aeval_X_left_eq_algebraMap (p : K[X]
) : p.aeval (X : K⟮X⟯) = algebraMap K[X] K⟮X⟯ p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.num_div_denom`：num_div_denom (x : K⟮X⟯) : algebraMap _ _ (num x)
 / algebraMap _ _ (denom x) = x
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `RatFunc.algebraMap_ne_zero`：algebraMap_ne_zero {x : K[X]} (hx : x != 0) 
: algebraMap K[X] K⟮X⟯ x != 0
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem minpolyX_aeval_X : (f.minpolyX K⟮f⟯).aeval (X : K⟮X⟯) = 0 := by
  simp only [aeval_sub, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, map_mul, aeval_C,
    IntermediateField.algebraMap_apply, coe_algebraMap]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _
/-
**RatFunc.eq_C_of_minpolyX_coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：eq_C_of_minpolyX_coeff_eq_zero (hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDe
gree = (0 : K⟮X⟯)) : exists c, f = C c
参数：hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : K⟮X⟯)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `RatFunc.denom_ne_zero`：denom_ne_zero (x : K⟮X⟯) : denom x != 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
-/
theorem eq_C_of_minpolyX_coeff_eq_zero
  (hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : K⟮X⟯)) : ∃ c, f = C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀, eq_div_iff ((_root_.map_ne_zero C).mpr
    (leadingCoeff_ne_zero.mpr f.denom_ne_zero)), eq_comm]
  simpa [sub_eq_zero] using hf
/-
**RatFunc.minpolyX_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：minpolyX_eq_zero_iff : (f.minpolyX K⟮f⟯) = 0 ↔ exists c, f = C c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RatFunc.eq_C_of_minpolyX_coeff_eq_zero`：eq_C_of_minpolyX_coeff_eq_zero (
hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : K⟮X⟯)) : exists c, f = C c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RatFunc.C_minpolyX`：C_minpolyX (x : K) : (C x).minpolyX K⟮C x⟯ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem minpolyX_eq_zero_iff : (f.minpolyX K⟮f⟯) = 0 ↔ ∃ c, f = C c :=
  ⟨fun h ↦ f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩
/-
**RatFunc.isAlgebraic_adjoin_simple_X** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：isAlgebraic_adjoin_simple_X (hf : ¬exists c, f = C c) : IsAlgebraic K⟮f⟯ (
X : K⟮X⟯)
参数：hf : ¬exists c, f = C c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RatFunc.minpolyX_eq_zero_iff`：minpolyX_eq_zero_iff : (f.minpolyX K⟮f⟯) =
 0 ↔ exists c, f = C c
· 使用定理 `RatFunc.minpolyX_aeval_X`：minpolyX_aeval_X : (f.minpolyX K⟮f⟯).aeval (X 
: K⟮X⟯) = 0
-/
theorem isAlgebraic_adjoin_simple_X (hf : ¬∃ c, f = C c) : IsAlgebraic K⟮f⟯ (X : K⟮X⟯) :=
  ⟨f.minpolyX K⟮f⟯, fun H ↦ hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩
/-
**RatFunc.isAlgebraic_adjoin_simple_X'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：isAlgebraic_adjoin_simple_X' (hf : ¬exists c, f = C c) : Algebra.IsAlgebra
ic K⟮f⟯ K⟮X⟯
参数：hf : ¬exists c, f = C c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.isAlgebraic_adjoin_simple`：isAlgebraic_adjoin_simple {
x : L} (hx : IsIntegral K x) : Algebra.IsAlgebraic K K⟮x⟯
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAlgebraic_iff_isIntegral`：isAlgebraic_iff_isIntegral {x : A} : IsAlgeb
raic K x ↔ IsIntegral K x
· 使用定理 `RatFunc.isAlgebraic_adjoin_simple_X`：isAlgebraic_adjoin_simple_X (hf : ¬
exists c, f = C c) : IsAlgebraic K⟮f⟯ (X : K⟮X⟯)
· 使用定理 `AlgEquiv.isAlgebraic`：AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B) [Algebra.IsAl
gebraic R A] : Algebra.IsAlgebraic R B
-/
theorem isAlgebraic_adjoin_simple_X' (hf : ¬∃ c, f = C c) :
    Algebra.IsAlgebraic K⟮f⟯ K⟮X⟯ := by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : K⟮X⟯)⟯ :=
    isAlgebraic_adjoin_simple <| isAlgebraic_iff_isIntegral.mp <| f.isAlgebraic_adjoin_simple_X hf
  exact (IntermediateField.adjoinXEquiv K⟮f⟯).isAlgebraic
/-
**RatFunc.natDegree_denom_le_natDegree_minpolyX** 是 Mathlib 中的一个定理，位于命名空间 `RatFu
nc`。
形式化陈述：natDegree_denom_le_natDegree_minpolyX (hf : ¬exists c, f = C c) : f.denom.
natDegree <= (f.minpolyX K⟮f⟯).natDegree
参数：hf : ¬exists c, f = C c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.le_natDegree_of_ne_zero`：le_natDegree_of_ne_zero (h : coeff p
 n != 0) : n <= natDegree p
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RatFunc.eq_C_of_minpolyX_coeff_eq_zero`：eq_C_of_minpolyX_coeff_eq_zero (
hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : K⟮X⟯)) : exists c, f = C c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem natDegree_denom_le_natDegree_minpolyX (hf : ¬∃ c, f = C c) :
    f.denom.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree :=
  le_natDegree_of_ne_zero fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

set_option backward.isDefEq.respectTransparency false in
/-
**RatFunc.natDegree_num_le_natDegree_minpolyX** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc
`。
形式化陈述：natDegree_num_le_natDegree_minpolyX (hf : ¬exists c, f = C c) : f.num.natD
egree <= (f.minpolyX K⟮f⟯).natDegree
参数：hf : ¬exists c, f = C c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Polynomial.le_natDegree_of_ne_zero`：le_natDegree_of_ne_zero (h : coeff p
 n != 0) : n <= natDegree p
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `RatFunc.num_ne_zero`：num_ne_zero {x : K⟮X⟯} (hx : x != 0) : num x != 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
（共 33 条，此处仅展示前 30 条）
-/
theorem natDegree_num_le_natDegree_minpolyX (hf : ¬∃ c, f = C c) :
    f.num.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree := by
  have f_ne_zero : f ≠ 0 := by
    rintro rfl
    exact hf ⟨0, (RingHom.map_zero C).symm⟩
  apply le_natDegree_of_ne_zero
  intro H
  replace H := congr($(H).val)
  simp only [coeff_sub, coeff_map, coeff_natDegree, coeff_C_mul, AddSubgroupClass.coe_sub,
    SubalgebraClass.coe_algebraMap, algebraMap_eq_C, MulMemClass.coe_mul, coe_algebraMap,
    ZeroMemClass.coe_zero] at H
  rw [sub_eq_zero, ← mul_right_inj' (inv_ne_zero f_ne_zero), ← mul_assoc, inv_mul_cancel₀ f_ne_zero,
    one_mul, ← eq_div_iff <| (_root_.map_ne_zero C).mpr <| Polynomial.leadingCoeff_ne_zero.mpr
    (num_ne_zero f_ne_zero), ← inv_inj, inv_inv, ← map_div₀, ← map_inv₀] at H
  exact hf ⟨_, H⟩
/-
**RatFunc.natDegree_minpolyX** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：natDegree_minpolyX : (f.minpolyX K⟮f⟯).natDegree = max f.num.natDegree f.d
enom.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RatFunc.C_minpolyX`：C_minpolyX (x : K) : (C x).minpolyX K⟮C x⟯ = 0
· 使用定理 `RatFunc.num_C`：num_C (c : K) : num (C c) = Polynomial.C c
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `RatFunc.denom_C`：denom_C (c : K) : denom (C c) = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.natDegree_sub_le`：natDegree_sub_le (p q : R[X]) : natDegree (
p - q) <= max (natDegree p) (natDegree q)
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.natDegree_C_mul`：natDegree_C_mul (a0 : a != 0) : (C a * p).na
tDegree = p.natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
（共 33 条，此处仅展示前 30 条）
-/
theorem natDegree_minpolyX :
    (f.minpolyX K⟮f⟯).natDegree = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    simp
  apply le_antisymm
  · have : (f.minpolyX K⟮f⟯).natDegree ≤ _ := natDegree_sub_le _ _
    rw [natDegree_map, natDegree_C_mul fun H ↦ hf ⟨0, by simpa [map_zero] using congr($(H).val)⟩,
      natDegree_map] at this
    exact this
  · exact max_le (natDegree_num_le_natDegree_minpolyX f hf) <| le_natDegree_of_ne_zero
      fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))
/-
**RatFunc.transcendental_of_ne_C** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：transcendental_of_ne_C (hf : ¬exists c, f = C c) : Transcendental K f
参数：hf : ¬exists c, f = C c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.isAlgebraic_adjoin_simple`：isAlgebraic_adjoin_simple {
x : L} (hx : IsIntegral K x) : Algebra.IsAlgebraic K K⟮x⟯
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.transcendental_iff_not_isAlgebraic`：Algebra.transcendental_iff_n
ot_isAlgebraic : Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A
· 使用定理 `Algebra.IsAlgebraic.trans`：∀ (R : Type u_1) (S : Type u_2) (A : Type u_3
) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_3 : Algebr
a R S] [inst_4 …
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `RatFunc.isAlgebraic_adjoin_simple_X'`：isAlgebraic_adjoin_simple_X' (hf :
 ¬exists c, f = C c) : Algebra.IsAlgebraic K⟮f⟯ K⟮X⟯
-/
theorem transcendental_of_ne_C (hf : ¬∃ c, f = C c) : Transcendental K f := by
  intro H
  have := isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K K⟮X⟯ := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
  exact tr <| Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

set_option backward.isDefEq.respectTransparency.types false in
/-
**RatFunc.irreducible_minpolyX'** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：irreducible_minpolyX' (hf : ¬exists c, f = C c) : Irreducible (f.minpolyX 
K[f])
参数：hf : ¬exists c, f = C c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RatFunc.transcendental_of_ne_C`：transcendental_of_ne_C (hf : ¬exists c, 
f = C c) : Transcendental K f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mapEquiv_apply`：∀ {R : Type u} {S : Type v} [inst : Semiring 
R] [inst_1 : Semiring S] (e : R ≃+* S) (a : Polynomial R),   (Polynomial.mapEqui
v e) a = Polyno…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MulEquiv.irreducible_iff`：MulEquiv.irreducible_iff : Irreducible (f x) ↔
 Irreducible x
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `Polynomial.X_mul_C`：X_mul_C (r : R) : X * C r = C r * X
（共 55 条，此处仅展示前 30 条）
-/
theorem irreducible_minpolyX' (hf : ¬∃ c, f = C c) : Irreducible (f.minpolyX K[f]) := by
  let e := Polynomial.algEquivOfTranscendental K f (f.transcendental_of_ne_C hf)
  let φ : K[X][X] := f.num.map (algebraMap ..) -
    Polynomial.C Polynomial.X * f.denom.map (algebraMap ..)
  have φ_map : φ.mapEquiv e.toRingEquiv = (f.minpolyX K[f]) := by
    simp only [algebraMap_eq, map_sub, mapEquiv_apply,
      AlgEquiv.toRingEquiv_toRingHom, algEquivOfTranscendental_coe, Polynomial.map_map, map_mul,
      map_C, RingHom.coe_coe, aeval_X, e, φ]
    congr 2 <;> ext <;> simp
  rw [← φ_map, MulEquiv.irreducible_iff]
  have : φ = Bivariate.swap
      (Polynomial.C f.num - Polynomial.X * Polynomial.C f.denom) := by
    simp only [X_mul_C, Bivariate.swap_apply, aevalAeval, aevalAevalEquiv, Equiv.coe_fn_mk,
      AlgHom.coe_comp, AlgHom.coe_restrictScalars', coe_aeval_eq_eval, Function.comp_apply,
      aeval_sub, aeval_C, algebraMap_def, coe_mapRingHom, map_mul, aeval_X, eval_sub,
      eval_map_algebraMap, Polynomial.eval_mul, Polynomial.eval_C]
    rw [mul_comm]
    rfl
  rw [this, MulEquiv.irreducible_iff]
  convert!
    irreducible_C_mul_X_add_C (neg_ne_zero.mpr f.denom_ne_zero)
      ((IsCoprime.neg_right_iff _ _).mpr f.isCoprime_num_denom).symm.isRelPrime using 1
  rw [add_comm, X_mul_C, map_neg, neg_mul]
  exact sub_eq_add_neg (Polynomial.C f.num) (Polynomial.C f.denom * Polynomial.X)
/-
**RatFunc.irreducible_minpolyX** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：irreducible_minpolyX (hf : ¬exists c, f = C c) : Irreducible (f.minpolyX K
⟮f⟯)
参数：hf : ¬exists c, f = C c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Transcendental.uniqueFactorizationMonoid_adjoin`：Transcendental.uniqueFa
ctorizationMonoid_adjoin [UniqueFactorizationMonoid R] {s : S} (h : Transcendent
al R s) : UniqueFactorizationMonoid (…
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `RatFunc.transcendental_of_ne_C`：transcendental_of_ne_C (hf : ¬exists c, 
f = C c) : Transcendental K f
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RatFunc.minpolyX_map`：minpolyX_map (A : Type*) [CommRing A] [Algebra K A
] [Algebra (Algebra.adjoin K {f}) A] (B : Type*) [CommRing B] [Algebra K B] [Alg
ebra K[f] …
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalge
braAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fiel
d E] [inst_2 : Algebra F E] (S : Set E) (X : Type u_3)   [inst_3 : SMul X F] …
· 使用定理 `Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map`：∀ {
R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : Field K] [inst_2 : Al
gebra R K] [IsFractionRing R K]   [IsDomain R] [IsGCDMono…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsFractionRingSubtypeMemSubalg
ebraAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fie
ld E] [inst_2 : Algebra F E] (S : Set E),   IsFractionRing ↥(Algebra.adjoin F …
· 使用定理 `instIsGCDMonoidOfUniqueFactorizationMonoid`：∀ (α : Type u_2) [inst : Com
mMonoidWithZero α] [UniqueFactorizationMonoid α], IsGCDMonoid α
· 使用定理 `Irreducible.isPrimitive`：∀ {R : Type u_1} [inst : CommSemiring R] [NoZer
oDivisors R] {p : Polynomial R},   Irreducible p → p.natDegree ≠ 0 → p.IsPrimiti
ve
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `RatFunc.irreducible_minpolyX'`：irreducible_minpolyX' (hf : ¬exists c, f 
= C c) : Irreducible (f.minpolyX K[f])
· 使用引理 `Polynomial.natDegree_map_le`：natDegree_map_le : natDegree (p.map f) <= n
atDegree p
· 使用定理 `RatFunc.eq_C_iff`：eq_C_iff (f : K⟮X⟯) : (exists c, f = C c) ↔ f.num.natD
egree = 0 ∧ f.denom.natDegree = 0
· 使用定理 `Nat.max_eq_zero_iff`：∀ {m n : ℕ}, max m n = 0 ↔ m = 0 ∧ n = 0
· 使用定理 `RatFunc.natDegree_minpolyX`：natDegree_minpolyX : (f.minpolyX K⟮f⟯).natDe
gree = max f.num.natDegree f.denom.natDegree
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem irreducible_minpolyX (hf : ¬∃ c, f = C c) : Irreducible (f.minpolyX K⟮f⟯) := by
  have : UniqueFactorizationMonoid K[f] :=
    (f.transcendental_of_ne_C hf).uniqueFactorizationMonoid_adjoin
  rw [← f.minpolyX_map K[f] K⟮f⟯,
    ← IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
  · exact f.irreducible_minpolyX' hf
  · apply (f.irreducible_minpolyX' hf).isPrimitive
    intro H
    have := natDegree_map_le (f := algebraMap K[f] K⟮f⟯) (p := f.minpolyX K[f])
    rw [f.minpolyX_map K[f] K⟮f⟯, H, nonpos_iff_eq_zero, f.natDegree_minpolyX,
      Nat.max_eq_zero_iff, ← f.eq_C_iff] at this
    exact hf this
/-
**RatFunc.finrank_eq_max_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc`。
形式化陈述：finrank_eq_max_natDegree : Module.finrank K⟮f⟯ K⟮X⟯ = max f.num.natDegree 
f.denom.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_simple_eq_bot_iff`：adjoin_simple_eq_bot_iff : F
⟮α⟯ = ⊥ ↔ α in (⊥ : IntermediateField F E)
· 使用定理 `IntermediateField.finrank_bot'`：finrank_bot' : finrank (⊥ : Intermediate
Field F E) E = finrank F E
· 使用定理 `Module.finrank_of_not_finite`：finrank_of_not_finite (h : ¬Module.Finite 
R M) : finrank R M = 0
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.transcendental_iff_not_isAlgebraic`：Algebra.transcendental_iff_n
ot_isAlgebraic : Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RatFunc.num_C`：num_C (c : K) : num (C c) = Polynomial.C c
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `RatFunc.denom_C`：denom_C (c : K) : denom (C c) = 1
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `IntermediateField.adjoin.finrank`：∀ {K : Type u} [inst : Field K] {L : T
ype u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegral K x → M
odule.finrank K ↥K⟮x⟯ …
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `RatFunc.isAlgebraic_adjoin_simple_X`：isAlgebraic_adjoin_simple_X (hf : ¬
exists c, f = C c) : IsAlgebraic K⟮f⟯ (X : K⟮X⟯)
· 使用定理 `RatFunc.instIsScalarTowerOfIsDomainOfPolynomial`：∀ (R₀ : Type u_1) (R : 
Type u_2) (A : Type u_3) [inst : CommSemiring R₀] [inst_1 : CommSemiring R] [ins
t_2 : CommRing A]   [IsDomain A] [ins…
（共 41 条，此处仅展示前 30 条）
-/
theorem finrank_eq_max_natDegree :
    Module.finrank K⟮f⟯ K⟮X⟯ = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c ∈ ⊥ from ⟨c, rfl⟩), finrank_bot',
      Module.finrank_of_not_finite fun H ↦ Algebra.transcendental_iff_not_isAlgebraic.mp
      transcendental <| Algebra.IsAlgebraic.of_finite K K⟮X⟯]
    simp
  rw [← (IntermediateField.adjoinXEquiv K⟮f⟯).toLinearEquiv.finrank_eq,
    adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral,
    ← minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X, mul_comm,
    natDegree_C_mul <| inv_ne_zero <| leadingCoeff_ne_zero.mpr fun H ↦
    hf ((minpolyX_eq_zero_iff f).mp H), natDegree_minpolyX]
/-
**RatFunc.IntermediateField.isAlgebraic_X** 是 Mathlib 中的一个定理，位于命名空间 `RatFunc.Int
ermediateField`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {E : IntermediateField K (RatFunc K)}, E
 ≠ ⊥ → IsAlgebraic (↥E) RatFunc.X
参数：RatFunc K；↥E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.not_le_iff_exists`：not_le_iff_exists : ¬p <= q ↔ exists x in p, 
x ∉ q
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `IsAlgebraic.tower_top_of_subalgebra_le`：IsAlgebraic.tower_top_of_subalge
bra_le {A B : Subalgebra R S} (hle : A <= B) {x : S} (h : IsAlgebraic A x) : IsA
lgebraic B x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_simple_le_iff`：adjoin_simple_le_iff {K : Interm
ediateField F E} : F⟮α⟯ <= K ↔ α in K
· 使用定理 `RatFunc.isAlgebraic_adjoin_simple_X`：isAlgebraic_adjoin_simple_X (hf : ¬
exists c, f = C c) : IsAlgebraic K⟮f⟯ (X : K⟮X⟯)
-/
theorem IntermediateField.isAlgebraic_X {E : IntermediateField K K⟮X⟯} (hE : E ≠ ⊥) :
    IsAlgebraic E (X : K⟮X⟯) := by
  rw [ne_eq, ← le_bot_iff, SetLike.not_le_iff_exists] at hE
  obtain ⟨f, hf₁, hf₂⟩ := hE
  exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁) <|
    f.isAlgebraic_adjoin_simple_X (by rintro ⟨c, rfl⟩; exact hf₂ ⟨c, rfl⟩)

end

end RatFunc

