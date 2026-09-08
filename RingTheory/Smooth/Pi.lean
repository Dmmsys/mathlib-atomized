/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Smooth.Basic

/-!

# Formal-smoothness of finite products of rings

## Main result

- `Algebra.FormallySmooth.pi_iff`: If `I` is finite, `Π i : I, A i` is `R`-formally-smooth
  if and only if each `A i` is `R`-formally-smooth.

-/

public section

namespace Algebra.FormallySmooth

variable {R : Type*} {I : Type*} (A : I → Type*)
variable [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]

/-
**Algebra.FormallySmooth.of_pi** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallySmooth
`。
形式化陈述：of_pi [FormallySmooth R (Π i, A i)] (i) : FormallySmooth R (A i)
参数：Π i, A i；i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.of_split`：∀ {R : Type u} {A : Type v} [inst : Com
mRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {P : Type u_2}   [inst_3 :
 CommRing P] [inst_4 …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.evalAlgHom_apply`：∀ {ι : Type u_1} (R : Type u_2) (A : ι → Type u_3) 
[inst : CommSemiring R] [inst_1 : (i : ι) → Semiring (A i)]   [inst_2 : (i : ι) 
→ Algebra…
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `Ideal.pow_mem_pow`：pow_mem_pow {x : R} (hx : x in I) (n : Nat) : x ^ n i
n I ^ n
（共 35 条，此处仅展示前 30 条）
-/
theorem of_pi [FormallySmooth R (Π i, A i)] (i) :
    FormallySmooth R (A i) := by
  classical
  fapply FormallySmooth.of_split (Pi.evalAlgHom R A i)
  · apply AlgHom.ofLinearMap
      ((Ideal.Quotient.mkₐ R _).toLinearMap.comp (LinearMap.single _ _ i))
    · change Ideal.Quotient.mk _ (Pi.single i 1) = 1
      rw [← (Ideal.Quotient.mk _).map_one, ← sub_eq_zero, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      have : Pi.single i 1 - 1 ∈ RingHom.ker (Pi.evalAlgHom R A i).toRingHom := by
        simp [RingHom.mem_ker]
      convert! neg_mem (Ideal.pow_mem_pow this 2) using 1
      simp [pow_two, sub_mul, mul_sub, ← Pi.single_mul]
    · intro x y
      change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _
      simp +instances only [AlgHom.toRingHom_eq_coe, LinearMap.coe_single, Pi.single_mul, map_mul]
  · ext x
    change (Pi.single i x) i = x
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.FormallySmooth.pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallySmoot
h`。
形式化陈述：pi_iff [Finite I] : FormallySmooth R (Π i, A i) ↔ forall i, FormallySmooth
 R (A i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Algebra.FormallySmooth.of_pi`：of_pi [FormallySmooth R (Π i, A i)] (i) : 
FormallySmooth R (A i)
· 使用定理 `Algebra.FormallySmooth.of_comp_surjective`：∀ {R : Type u} {A : Type v} [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   (∀ ⦃B : Type 
(max u v)⦄ [inst_3 : CommRing B…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.pow_mem_pow`：pow_mem_pow {x : R} (hx : x in I) (n : Nat) : x ^ n i
n I ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用引理 `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`：CompleteOrthogona
lIdempotents.lift_of_isNilpotent_ker (h : forall x in RingHom.ker f, IsNilpotent
 x) {e : I -> S} (he : CompleteOrthogonalId…
· 使用引理 `CompleteOrthogonalIdempotents.map`：CompleteOrthogonalIdempotents.map (he
 : CompleteOrthogonalIdempotents e) : CompleteOrthogonalIdempotents (f ∘ e) wher
e __
· 使用引理 `CompleteOrthogonalIdempotents.single`：CompleteOrthogonalIdempotents.sing
le {I : Type*} [Fintype I] [DecidableEq I] (R : I -> Type*) [forall i, Semiring 
(R i)] : CompleteOrthogona…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用引理 `CompleteOrthogonalIdempotents.bijective_pi`：CompleteOrthogonalIdempotent
s.bijective_pi (he : CompleteOrthogonalIdempotents e) : Function.Bijective (Ring
Hom.pi fun i => Ideal.Quotient.m…
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
· 使用定理 `AlgHom.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Ideal.instIsTwoSidedMapRingHomOfRingHomSurjective`：∀ {R : Type u} {S : T
ype v} [inst : Semiring R] [inst_1 : Semiring S] (f : R →+* S) [RingHomSurjectiv
e f] (I : Ideal R)   [I.IsTwoSided], (I…
· 使用定理 `Ideal.Quotient.instRingHomSurjectiveQuotientMk`：∀ {R : Type u} [inst : R
ing R] {I : Ideal R} [inst_1 : I.IsTwoSided], RingHomSurjective (Ideal.Quotient.
mk I)
· 使用引理 `Ideal.ker_quotientMap_mk`：ker_quotientMap_mk {I J : Ideal R} [I.IsTwoSid
ed] [J.IsTwoSided] : RingHom.ker (quotientMap (J.map _) (Quotient.mk I) le_comap
_map) = I.map …
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
（共 91 条，此处仅展示前 30 条）
-/
theorem pi_iff [Finite I] :
    FormallySmooth R (Π i, A i) ↔ ∀ i, FormallySmooth R (A i) := by
  classical
  cases nonempty_fintype I
  constructor
  · exact fun _ ↦ of_pi A
  · refine fun H ↦ .of_comp_surjective fun B _ _ J hJ g ↦ ?_
    have hJ' (x) (hx : x ∈ RingHom.ker (Ideal.Quotient.mk J)) : IsNilpotent x := by
      refine ⟨2, show x ^ 2 ∈ (⊥ : Ideal B) from ?_⟩
      rw [← hJ]
      exact Ideal.pow_mem_pow (by simpa using! hx) 2
    obtain ⟨e, he, he'⟩ := ((CompleteOrthogonalIdempotents.single A).map
      g.toRingHom).lift_of_isNilpotent_ker (Ideal.Quotient.mk J) hJ'
        fun _ ↦ Ideal.Quotient.mk_surjective _
    replace he' : ∀ i, Ideal.Quotient.mk J (e i) = g (Pi.single i 1) := congr_fun he'
    let iso : B ≃ₐ[R] ∀ i, B ⧸ Ideal.span {1 - e i} :=
      { __ := AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ R _
        __ := Equiv.ofBijective _ he.bijective_pi }
    let J' := fun i ↦ J.map (Ideal.Quotient.mk (Ideal.span {1 - e i}))
    let ι : ∀ i, (B ⧸ J →ₐ[R] (B ⧸ _) ⧸ J' i) := fun i ↦ Ideal.quotientMapₐ _
      (IsScalarTower.toAlgHom R B _) Ideal.le_comap_map
    have hι : ∀ i x, ι i x = 0 → (e i) * x = 0 := by
      intro i x hix
      have : x ∈ (Ideal.span {1 - e i}).map (Ideal.Quotient.mk J) := by
        rw [← Ideal.ker_quotientMap_mk]; exact hix
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at this
      obtain ⟨c, rfl⟩ := this
      rw [← mul_assoc, ← map_mul, mul_sub, mul_one, (he.idem i).eq, sub_self, map_zero, zero_mul]
    have : ∀ i : I, ∃ a : A i →ₐ[R] B ⧸ Ideal.span {1 - e i}, ∀ x,
        Ideal.Quotient.mk (J' i) (a x) = ι i (g (Pi.single i x)) := by
      intro i
      let g' : A i →ₐ[R] (B ⧸ _) ⧸ (J' i) := by
        apply AlgHom.ofLinearMap (((ι i).comp g).toLinearMap ∘ₗ LinearMap.single _ _ i)
        · suffices Ideal.Quotient.mk (Ideal.span {1 - e i}) (e i) = 1 by simp [ι, ← he', this]
          rw [← (Ideal.Quotient.mk _).map_one, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
            Ideal.mem_span_singleton]
        · intro x y; simp [Pi.single_mul]
      obtain ⟨a, ha⟩ := FormallySmooth.comp_surjective _ _ (I := J' i)
        (by rw [← Ideal.map_pow, hJ, Ideal.map_bot]) g'
      exact ⟨a, AlgHom.congr_fun ha⟩
    choose a ha using this
    use iso.symm.toAlgHom.comp (AlgHom.pi fun i ↦ (a i).comp (Pi.evalAlgHom R A i))
    ext x; rw [← AlgHom.toLinearMap_apply, ← AlgHom.toLinearMap_apply]; congr 1
    ext i x
    simp only [AlgHom.comp_toLinearMap, AlgEquiv.toAlgHom_toLinearMap,
      LinearMap.coe_comp, LinearMap.coe_single, Function.comp_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (a i x)
    have hy' : Ideal.Quotient.mk (Ideal.span {1 - e i}) (y * e i) = a i x := by
      have : Ideal.Quotient.mk (Ideal.span {1 - e i}) (e i) = 1 := by
        rw [← (Ideal.Quotient.mk _).map_one, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
          Ideal.mem_span_singleton]
      rw [map_mul, this, hy, mul_one]
    trans Ideal.Quotient.mk J (y * e i)
    · congr 1; apply iso.injective; ext j
      suffices a j (Pi.single i x j) = Ideal.Quotient.mk _ (y * e i) by simpa using! this
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same, hy']
      · have : Ideal.Quotient.mk (Ideal.span {1 - e j}) (e i) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
          refine ⟨e i, by simp [he.ortho (Ne.symm hij), sub_mul]⟩
        rw [Pi.single_eq_of_ne (Ne.symm hij), map_zero, map_mul, this, mul_zero]
    · have : ι i (Ideal.Quotient.mk J (y * e i)) = ι i (g (Pi.single i x)) := by
        rw [← ha, ← hy']
        simp only [Ideal.quotient_map_mkₐ, IsScalarTower.coe_toAlgHom',
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mkₐ_eq_mk, ι]
      rw [← sub_eq_zero, ← map_sub] at this
      replace this := hι _ _ this
      rwa [mul_sub, ← map_mul, mul_comm, mul_assoc, (he.idem i).eq, he', ← map_mul, ← Pi.single_mul,
        one_mul, sub_eq_zero] at this
/-
**Algebra.FormallySmooth.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallySmooth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite I] [∀ i, FormallySmooth R (A i)] : FormallySmooth R (Π i, A i) :=
  (pi_iff _).mpr ‹_›

end Algebra.FormallySmooth

