/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import Mathlib.Algebra.Ring.Torsion

/-!
# Structural lemmas about finite crystallographic root pairings

In this file we gather basic lemmas necessary for the classification of finite crystallographic
root pairings.

## Main results:

* `RootPairing.coxeterWeightIn_mem_set_of_isCrystallographic`: the Coxeter weights of a finite
  crystallographic root pairing belong to the set `{0, 1, 2, 3, 4}`.
* `RootPairing.root_sub_root_mem_of_pairingIn_pos`: if `α ≠ β` are both roots of a finite
  crystallographic root pairing, and the pairing of `α` with `β` is positive, then `α - β` is also
  a root.
* `RootPairing.root_add_root_mem_of_pairingIn_neg`: if `α ≠ -β` are both roots of a finite
  crystallographic root pairing, and the pairing of `α` with `β` is negative, then `α + β` is also
  a root.

-/

public section

noncomputable section

open Function Set
open Submodule (span)
open FaithfulSMul (algebraMap_injective)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable (P : RootPairing ι R M N) [Finite ι]

local notation "Φ" => range P.root
local notation "α" => P.root

/-- SGA3 XXI Prop. 2.3.1 -/
/-
**RootPairing.coxeterWeightIn_le_four** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coxeterWeightIn_le_four (S : Type*) [CommRing S] [LinearOrder S] [IsStrict
OrderedRing S] [Algebra S R] [FaithfulSMul S R] [Module S M] [IsScalarTower S R 
M] [P.IsValuedIn S] (i j : ι) : P.coxeterWeightIn S i j <= 4
参数：S : Type*；i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RootPairing.RootPositiveForm.exists_pos_eq`：∀ {ι : Type u_1} {R : Type u
_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [inst_1 :
 LinearOrder S] [inst_2 : CommRi…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.RootPositiveForm.algebraMap_rootLength`：∀ {ι : Type u_1} {R 
: Type u_2} {S : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing S]   [
inst_1 : LinearOrder S] [inst_2 : CommRi…
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `four_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Partial
Order α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 4
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用引理 `LinearMap.BilinForm.apply_sq_le_of_symm`：apply_sq_le_of_symm (hs : foral
l x, 0 <= B x x) (hB : B.IsSymm) (x y : M) : (B x y) ^ 2 <= (B x x) * (B y y)
· 使用引理 `RootPairing.zero_le_posForm`：zero_le_posForm (x : span S (range P.root))
 : 0 <= (P.posRootForm S).posForm x x
· 使用引理 `RootPairing.RootPositiveForm.isSymm_posForm`：isSymm_posForm : B.posForm.
IsSymm where eq x y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.rootForm_symmetric`：rootForm_symmetric : LinearMap.IsSymm P.
RootForm
· 使用引理 `RootPairing.rootForm_reflection_reflection_apply`：rootForm_reflection_re
flection_apply (i : ι) (x y : M) : P.RootForm (P.reflection i x) (P.reflection i
 y) = P.RootForm x y
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
SGA3 XXI Prop. 2.3.1
-/
lemma coxeterWeightIn_le_four (S : Type*)
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [Algebra S R] [FaithfulSMul S R]
    [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] (i j : ι) :
    P.coxeterWeightIn S i j ≤ 4 := by
  have : Fintype ι := Fintype.ofFinite ι
  let ri : span S Φ := ⟨α i, Submodule.subset_span (mem_range_self _)⟩
  let rj : span S Φ := ⟨α j, Submodule.subset_span (mem_range_self _)⟩
  set li := (P.posRootForm S).rootLength i
  set lj := (P.posRootForm S).rootLength j
  set lij := (P.posRootForm S).posForm ri rj
  obtain ⟨si, hsi, hsi'⟩ := (P.posRootForm S).exists_pos_eq i
  obtain ⟨sj, hsj, hsj'⟩ := (P.posRootForm S).exists_pos_eq j
  replace hsi' : si = li := algebraMap_injective S R <| by simpa [li] using hsi'
  replace hsj' : sj = lj := algebraMap_injective S R <| by simpa [lj] using hsj'
  rw [hsi'] at hsi
  rw [hsj'] at hsj
  have cs : 4 * lij ^ 2 ≤ 4 * (li * lj) := by
    rw [mul_le_mul_iff_right₀ four_pos]
    exact (P.posRootForm S).posForm.apply_sq_le_of_symm (zero_le_posForm _ _ ·)
      (P.posRootForm S).isSymm_posForm ri rj
  have key : 4 • lij ^ 2 = P.coxeterWeightIn S i j • (li * lj) := by
    apply algebraMap_injective S R
    simpa [map_ofNat, lij, posRootForm, ri, rj, li, lj] using
       P.four_smul_rootForm_sq_eq_coxeterWeight_smul i j
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] at key
  rwa [key, mul_le_mul_iff_left₀ (by positivity)] at cs

variable [CharZero R] [P.IsCrystallographic] (i j : ι)
/-
**RootPairing.coxeterWeightIn_mem_set_of_isCrystallographic** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing`。
形式化陈述：coxeterWeightIn_mem_set_of_isCrystallographic : P.coxeterWeightIn Int i j 
in ({0, 1, 2, 3, 4} : Set Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.coxeterWeight_nonneg`：coxeterWeight_nonneg [IsStrictOrderedR
ing S] : 0 <= P.coxeterWeightIn S i j
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Int.eq_ofNat_of_zero_le`：∀ {a : ℤ}, 0 ≤ a → ∃ n, a = ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RootPairing.coxeterWeightIn_le_four`：coxeterWeightIn_le_four (S : Type*)
 [CommRing S] [LinearOrder S] [IsStrictOrderedRing S] [Algebra S R] [FaithfulSMu
l S R] [Module S M] [IsSc…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma coxeterWeightIn_mem_set_of_isCrystallographic :
    P.coxeterWeightIn ℤ i j ∈ ({0, 1, 2, 3, 4} : Set ℤ) := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hcn⟩ : ∃ n : ℕ, P.coxeterWeightIn ℤ i j = n := by
    have : 0 ≤ P.coxeterWeightIn ℤ i j := by
      simpa only [P.algebraMap_coxeterWeightIn] using P.coxeterWeight_nonneg (P.posRootForm ℤ) i j
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le this
    exact ⟨n, by simp [hn]⟩
  have : P.coxeterWeightIn ℤ i j ≤ 4 := P.coxeterWeightIn_le_four ℤ i j
  simp only [hcn, mem_insert_iff, mem_singleton_iff] at this ⊢
  norm_cast at this ⊢
  lia

variable [IsDomain R]
-- This makes an `IsAddTorsionFree R` instance available, which `grind` needs below.
open scoped IsDomain
/-
**RootPairing.pairingIn_pairingIn_mem_set_of_isCrystallographic** 是 Mathlib 中的一个
引理，位于命名空间 `RootPairing`。
形式化陈述：pairingIn_pairingIn_mem_set_of_isCrystallographic : (P.pairingIn Int i j, 
P.pairingIn Int j i) in ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-
2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1), (4, 1), (1, 4), (-4, -1), (-1, -4), 
(2, 2), (-2, -2)} : Set (Int × Int))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.mul_mem_zero_one_two_three_four_iff`：mul_mem_zero_one_two_three_four
_iff {a b : Int} (h₀ : a = 0 ↔ b = 0) : a * b in ({0, 1, 2, 3, 4} : Set Int) ↔ (
a, b) in ({ (0, 0), (1, 1), (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用引理 `RootPairing.pairing_eq_zero_iff'`：pairing_eq_zero_iff' [NeZero (2 : R)] 
[IsDomain R] : P.pairing i j = 0 ↔ P.pairing j i = 0
· 使用引理 `RootPairing.coxeterWeightIn_mem_set_of_isCrystallographic`：coxeterWeight
In_mem_set_of_isCrystallographic : P.coxeterWeightIn Int i j in ({0, 1, 2, 3, 4}
 : Set Int)
-/
lemma pairingIn_pairingIn_mem_set_of_isCrystallographic :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1), (4, 1), (1, 4), (-4, -1), (-1, -4), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  refine (Int.mul_mem_zero_one_two_three_four_iff ?_).mp
    (P.coxeterWeightIn_mem_set_of_isCrystallographic i j)
  simpa [← P.algebraMap_pairingIn ℤ] using P.pairing_eq_zero_iff' (i := i) (j := j)
/-
**RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed** 是 Mathlib 中的一个
引理，位于命名空间 `RootPairing`。
形式化陈述：pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] : (P.pairi
ngIn Int i j, P.pairingIn Int j i) in ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1)
, (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1), (2, 2), (-2, -2)} : Se
t (Int × Int))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.pairingIn_same`：pairingIn_same [FaithfulSMul S R] [P.IsValue
dIn S] (i : ι) : P.pairingIn S i i = 2
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `RootPairing.pairingIn.congr_simp`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_left`：pairingIn_reflectionPerm
_self_left [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S (P.refl
ectionPerm i i) j = - P.pairingIn S …
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_right`：pairingIn_reflectionPer
m_self_right [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S i (P.
reflectionPerm j j) = - P.pairingIn S…
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystallographic`：pairingIn
_pairingIn_mem_set_of_isCrystallographic : (P.pairingIn Int i j, P.pairingIn Int
 j i) in ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1)…
· 使用引理 `RootPairing.coxeterWeightIn_ne_four`：coxeterWeightIn_ne_four [P.IsReduce
d] (h : i != j) (h' : P.root i != -P.root j) : P.coxeterWeightIn S i j != 4
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 37 条，此处仅展示前 30 条）
-/
lemma pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rcases eq_or_ne i j with rfl | h₁; · simp
  rcases eq_or_ne (α i) (-α j) with h₂ | h₂; · simp_all
  have aux₁ := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  have aux₂ : P.pairingIn ℤ i j * P.pairingIn ℤ j i ≠ 4 := P.coxeterWeightIn_ne_four ℤ h₁ h₂
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
/-
**RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'** 是 Mathlib 中的一
个引理，位于命名空间 `RootPairing`。
形式化陈述：pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' [P.IsReduced] (hij : α 
i != α j) (hij' : α i != -α j) : (P.pairingIn Int i j, P.pairingIn Int j i) in (
{(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (
-1, -3), (-3, -1)} : Set (Int × Int))
参数：hij : α i != α j；hij' : α i != -α j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed`：pairingIn
_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] : (P.pairingIn Int i j, P
.pairingIn Int j i) in ({(0, 0), (1, 1), (-1, -1), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' [P.IsReduced]
    (hij : α i ≠ α j) (hij' : α i ≠ -α j) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3),
        (-3, -1)} : Set (ℤ × ℤ)) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  simp_all

variable {P} in
/-
**RootPairing.RootPositiveForm.rootLength_le_of_pairingIn_eq** 是 Mathlib 中的一个定理，
位于命名空间 `RootPairing.RootPositiveForm`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [Finite ι] [
inst_6 : CharZero R] [inst_7 : P.IsCrystallographic] [IsDomain R] (B : RootPairi
ng.RootPositiveForm ℤ P)   {i j : ι}, P.pairingIn ℤ i j = -1 ∨ P.pairingIn ℤ i j
 = 1 → B.rootLength i ≤ B.rootLength j
参数：B : RootPairing.RootPositiveForm ℤ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystallographic`：pairingIn
_pairingIn_mem_set_of_isCrystallographic : (P.pairingIn Int i j, P.pairingIn Int
 j i) in ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用引理 `RootPairing.RootPositiveForm.pairingIn_mul_eq_pairingIn_mul_swap`：pairin
gIn_mul_eq_pairingIn_mul_swap : P.pairingIn S j i * B.rootLength i = P.pairingIn
 S i j * B.rootLength j
· 使用引理 `RootPairing.RootPositiveForm.rootLength_pos`：rootLength_pos (i : ι) : 0 
< B.rootLength i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma RootPositiveForm.rootLength_le_of_pairingIn_eq (B : P.RootPositiveForm ℤ) {i j : ι}
    (hij : P.pairingIn ℤ i j = -1 ∨ P.pairingIn ℤ i j = 1) :
    B.rootLength i ≤ B.rootLength j := by
  have h : (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(1, 1), (1, 2), (1, 3), (1, 4), (-1, -1), (-1, -2), (-1, -3), (-1, -4)} : Set (ℤ × ℤ)) := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at h
  have h' := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases h with hij' | hij' | hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hij'.1, hij'.2] at h' <;> lia

variable {P} in
/-
**RootPairing.RootPositiveForm.rootLength_lt_of_pairingIn_notMem** 是 Mathlib 中的一
个定理，位于命名空间 `RootPairing.RootPositiveForm`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [Finite ι] [
inst_6 : CharZero R] [inst_7 : P.IsCrystallographic] [IsDomain R] (B : RootPairi
ng.RootPositiveForm ℤ P)   {i j : ι},   P.root i ≠ P.root j → P.root i ≠ -P.root
 j → P.pairingIn ℤ i j ∉ {-1, 0, 1} → B.rootLength j < B.rootLength i
参数：B : RootPairing.RootPositiveForm ℤ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystallographic`：pairingIn
_pairingIn_mem_set_of_isCrystallographic : (P.pairingIn Int i j, P.pairingIn Int
 j i) in ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `RootPairing.RootPositiveForm.pairingIn_mul_eq_pairingIn_mul_swap`：pairin
gIn_mul_eq_pairingIn_mul_swap : P.pairingIn S j i * B.rootLength i = P.pairingIn
 S i j * B.rootLength j
· 使用引理 `RootPairing.RootPositiveForm.rootLength_pos`：rootLength_pos (i : ι) : 0 
< B.rootLength i
-/
lemma RootPositiveForm.rootLength_lt_of_pairingIn_notMem
    (B : P.RootPositiveForm ℤ) {i j : ι}
    (hne : α i ≠ α j) (hne' : α i ≠ -α j)
    (hij : P.pairingIn ℤ i j ∉ ({-1, 0, 1} : Set ℤ)) :
    B.rootLength j < B.rootLength i := by
  have hij' : P.pairingIn ℤ i j = -3 ∨ P.pairingIn ℤ i j = -2 ∨ P.pairingIn ℤ i j = 2 ∨
      P.pairingIn ℤ i j = 3 ∨ P.pairingIn ℤ i j = -4 ∨ P.pairingIn ℤ i j = 4 := by
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  have aux₁ : P.pairingIn ℤ j i = -1 ∨ P.pairingIn ℤ j i = 1 := by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  have aux₂ := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have hi := B.rootLength_pos i
  rcases aux₁ with hji | hji <;> rcases hij' with hij' | hij' | hij' | hij' | hij' | hij' <;>
  rw [hji, hij'] at aux₂ <;> lia

variable {i j} in
/-
**RootPairing.pairingIn_pairingIn_mem_set_of_length_eq** 是 Mathlib 中的一个引理，位于命名空间
 `RootPairing`。
形式化陈述：pairingIn_pairingIn_mem_set_of_length_eq {B : P.InvariantForm} (len_eq : B
.form (α i) (α i) = B.form (α j) (α j)) : (P.pairingIn Int i j, P.pairingIn Int 
j i) in ({(0, 0), (1, 1), (-1, -1), (2, 2), (-2, -2)} : Set (Int × Int))
参数：len_eq : B.form (α i) (α i) = B.form (α j) (α j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `RootPairing.InvariantForm.ne_zero`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用引理 `RootPairing.InvariantForm.pairing_mul_eq_pairing_mul_swap`：pairing_mul_e
q_pairing_mul_swap : P.pairing j i * B.form (P.root i) (P.root i) = P.pairing i 
j * B.form (P.root j) (P.root j)
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystallographic`：pairingIn
_pairingIn_mem_set_of_isCrystallographic : (P.pairingIn Int i j, P.pairingIn Int
 j i) in ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
-/
lemma pairingIn_pairingIn_mem_set_of_length_eq {B : P.InvariantForm}
    (len_eq : B.form (α i) (α i) = B.form (α j) (α j)) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(0, 0), (1, 1), (-1, -1), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  replace len_eq : P.pairingIn ℤ i j = P.pairingIn ℤ j i := by
    simp only [← (FaithfulSMul.algebraMap_injective ℤ R).eq_iff, algebraMap_pairingIn]
    exact mul_right_cancel₀ (B.ne_zero j) (len_eq ▸ B.pairing_mul_eq_pairing_mul_swap j i)
  have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

variable {i j} in
/-
**RootPairing.pairingIn_pairingIn_mem_set_of_length_eq_of_ne** 是 Mathlib 中的一个引理，
位于命名空间 `RootPairing`。
形式化陈述：pairingIn_pairingIn_mem_set_of_length_eq_of_ne {B : P.InvariantForm} (len_
eq : B.form (α i) (α i) = B.form (α j) (α j)) (ne : i != j) (ne' : α i != -α j) 
: (P.pairingIn Int i j, P.pairingIn Int j i) in ({(0, 0), (1, 1), (-1, -1)} : Se
t (Int × Int))
参数：len_eq : B.form (α i) (α i) = B.form (α j) (α j)；ne : i != j；ne' : α i != -α 
j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_length_eq`：pairingIn_pairingI
n_mem_set_of_length_eq {B : P.InvariantForm} (len_eq : B.form (α i) (α i) = B.fo
rm (α j) (α j)) : (P.pairingIn Int i j, P.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma pairingIn_pairingIn_mem_set_of_length_eq_of_ne {B : P.InvariantForm}
    (len_eq : B.form (α i) (α i) = B.form (α j) (α j))
    (ne : i ≠ j) (ne' : α i ≠ -α j) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈ ({(0, 0), (1, 1), (-1, -1)} : Set (ℤ × ℤ)) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have := P.pairingIn_pairingIn_mem_set_of_length_eq len_eq
  simp_all

omit [Finite ι] in
/-
**RootPairing.coxeterWeightIn_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
`。
形式化陈述：coxeterWeightIn_eq_zero_iff : P.coxeterWeightIn Int i j = 0 ↔ P.pairingIn 
Int i j = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FaithfulSMul.algebraMap_eq_zero_iff`：algebraMap_eq_zero_iff {r : R} : al
gebraMap R A r = 0 ↔ r = 0
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `RootPairing.pairing_eq_zero_iff'`：pairing_eq_zero_iff' [NeZero (2 : R)] 
[IsDomain R] : P.pairing i j = 0 ↔ P.pairing j i = 0
· 使用定理 `RootPairing.IsOrthogonal.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _
root_.Module R M] […
· 使用引理 `RootPairing.coxeterWeight_zero_iff_isOrthogonal`：coxeterWeight_zero_iff_
isOrthogonal [NeZero (2 : R)] [IsDomain R] : P.coxeterWeight i j = 0 ↔ P.IsOrtho
gonal i j
· 使用定理 `RootPairing.algebraMap_coxeterWeightIn`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `RootPairing.coxeterWeightIn.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma coxeterWeightIn_eq_zero_iff :
    P.coxeterWeightIn ℤ i j = 0 ↔ P.pairingIn ℤ i j = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [coxeterWeightIn, h, zero_mul]⟩
  rwa [← (algebraMap_injective ℤ R).eq_iff, map_zero, algebraMap_coxeterWeightIn,
    RootPairing.coxeterWeight_zero_iff_isOrthogonal, IsOrthogonal,
    P.pairing_eq_zero_iff' (i := j) (j := i), and_self, ← P.algebraMap_pairingIn ℤ,
    FaithfulSMul.algebraMap_eq_zero_iff] at h

variable {i j}
/-
**RootPairing.root_sub_root_mem_of_pairingIn_pos** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
形式化陈述：root_sub_root_mem_of_pairingIn_pos (h : 0 < P.pairingIn Int i j) (h' : i !
= j) : α i - α j in Φ
参数：h : 0 < P.pairingIn Int i j；h' : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `RootPairing.coxeterWeightIn_mem_set_of_isCrystallographic`：coxeterWeight
In_mem_set_of_isCrystallographic : P.coxeterWeightIn Int i j in ({0, 1, 2, 3, 4}
 : Set Int)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RootPairing.linearIndependent_iff_coxeterWeightIn_ne_four`：linearIndepen
dent_iff_coxeterWeightIn_ne_four : LinearIndependent R ![P.root i, P.root j] ↔ P
.coxeterWeightIn S i j != 4
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.coxeterWeightIn_eq_zero_iff`：coxeterWeightIn_eq_zero_iff : P
.coxeterWeightIn Int i j = 0 ↔ P.pairingIn Int i j = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `RootPairing.reflection_apply_root`：reflection_apply_root : P.reflection 
i (P.root j) = P.root j - (P.pairing j i) • P.root i
· 使用引理 `RootPairing.neg_mem_range_root_iff`：neg_mem_range_root_iff {x : M} : -x 
in range P.root ↔ x in range P.root
（共 51 条，此处仅展示前 30 条）
-/
lemma root_sub_root_mem_of_pairingIn_pos (h : 0 < P.pairingIn ℤ i j) (h' : i ≠ j) :
    α i - α j ∈ Φ := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  by_cases hli : LinearIndependent R ![α i, α j]
  · -- The case where the two roots are linearly independent
    suffices P.pairingIn ℤ i j = 1 ∨ P.pairingIn ℤ j i = 1 by
      rcases this with h₁ | h₁
      · replace h₁ : P.pairing i j = 1 := by simpa [← P.algebraMap_pairingIn ℤ]
        exact ⟨P.reflectionPerm j i, by simpa [h₁] using P.reflection_apply_root j i⟩
      · replace h₁ : P.pairing j i = 1 := by simpa [← P.algebraMap_pairingIn ℤ]
        rw [← neg_mem_range_root_iff, neg_sub]
        exact ⟨P.reflectionPerm i j, by simpa [h₁] using P.reflection_apply_root i j⟩
    have : P.coxeterWeightIn ℤ i j ∈ ({1, 2, 3} : Set _) := by
      have aux₁ := P.coxeterWeightIn_mem_set_of_isCrystallographic i j
      have aux₂ := (linearIndependent_iff_coxeterWeightIn_ne_four P ℤ).mp hli
      have aux₃ : P.coxeterWeightIn ℤ i j ≠ 0 := by
        simpa only [ne_eq, P.coxeterWeightIn_eq_zero_iff] using h.ne'
      simp_all
    simp_rw [coxeterWeightIn, Int.mul_mem_one_two_three_iff, mem_insert_iff, mem_singleton_iff,
      Prod.mk.injEq] at this
    lia
  · -- The case where the two roots are linearly dependent
    have : (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈ ({(1, 4), (2, 2), (4, 1)} : Set _) := by
      have := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
      replace hli : P.pairingIn ℤ i j * P.pairingIn ℤ j i = 4 :=
        (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hli
      aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at this
    rcases this with hij | hij | hij
    · rw [(P.pairingIn_one_four_iff ℤ i j).mp hij, two_smul, sub_add_cancel_right]
      exact neg_root_mem P i
    · rw [P.pairingIn_two_two_iff] at hij
      contradiction
    · rw [and_comm] at hij
      simp [(P.pairingIn_one_four_iff ℤ j i).mp hij, two_smul]

/-- If two roots make an obtuse angle then their sum is a root (provided it is not zero).

See `RootPairing.pairingIn_le_zero_of_root_add_mem` for a partial converse. -/
/-
**RootPairing.root_add_root_mem_of_pairingIn_neg** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
形式化陈述：root_add_root_mem_of_pairingIn_neg (h : P.pairingIn Int i j < 0) (h' : α i
 != -α j) : α i + α j in Φ
参数：h : P.pairingIn Int i j < 0；h' : α i != -α j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_right`：pairingIn_reflectionPer
m_self_right [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S i (P.
reflectionPerm j j) = - P.pairingIn S…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用引理 `RootPairing.root_sub_root_mem_of_pairingIn_pos`：root_sub_root_mem_of_pai
ringIn_pos (h : 0 < P.pairingIn Int i j) (h' : i != j) : α i - α j in Φ

--- 原说明 ---
If two roots make an obtuse angle then their sum is a root (provided it is not z
ero).

See `RootPairing.pairingIn_le_zero_of_root_add_mem` for a partial converse.
-/
lemma root_add_root_mem_of_pairingIn_neg (h : P.pairingIn ℤ i j < 0) (h' : α i ≠ -α j) :
    α i + α j ∈ Φ := by
  let _i := P.indexNeg
  replace h : 0 < P.pairingIn ℤ i (-j) := by simpa
  replace h' : i ≠ -j := by contrapose h'; simp [h']
  simpa using P.root_sub_root_mem_of_pairingIn_pos h h'
/-
**RootPairing.pairingIn_eq_zero_of_add_notMem_of_sub_notMem** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing`。
形式化陈述：pairingIn_eq_zero_of_add_notMem_of_sub_notMem (hp : i != j) (hn : α i != -
α j) (h_add : α i + α j ∉ Φ) (h_sub : α i - α j ∉ Φ) : P.pairingIn Int i j = 0
参数：hp : i != j；hn : α i != -α j；h_add : α i + α j ∉ Φ；h_sub : α i - α j ∉ Φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `RootPairing.root_sub_root_mem_of_pairingIn_pos`：root_sub_root_mem_of_pai
ringIn_pos (h : 0 < P.pairingIn Int i j) (h' : i != j) : α i - α j in Φ
· 使用引理 `RootPairing.root_add_root_mem_of_pairingIn_neg`：root_add_root_mem_of_pai
ringIn_neg (h : P.pairingIn Int i j < 0) (h' : α i != -α j) : α i + α j in Φ
-/
lemma pairingIn_eq_zero_of_add_notMem_of_sub_notMem (hp : i ≠ j) (hn : α i ≠ -α j)
    (h_add : α i + α j ∉ Φ) (h_sub : α i - α j ∉ Φ) :
    P.pairingIn ℤ i j = 0 := by
  apply le_antisymm
  · contrapose! h_sub
    exact root_sub_root_mem_of_pairingIn_pos P h_sub hp
  · contrapose! h_add
    exact root_add_root_mem_of_pairingIn_neg P h_add hn
/-
**RootPairing.pairing_eq_zero_of_add_notMem_of_sub_notMem** 是 Mathlib 中的一个引理，位于命
名空间 `RootPairing`。
形式化陈述：pairing_eq_zero_of_add_notMem_of_sub_notMem (hp : i != j) (hn : α i != -α 
j) (h_add : α i + α j ∉ Φ) (h_sub : α i - α j ∉ Φ) : P.pairing i j = 0
参数：hp : i != j；hn : α i != -α j；h_add : α i + α j ∉ Φ；h_sub : α i - α j ∉ Φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用引理 `RootPairing.pairingIn_eq_zero_of_add_notMem_of_sub_notMem`：pairingIn_eq_
zero_of_add_notMem_of_sub_notMem (hp : i != j) (hn : α i != -α j) (h_add : α i +
 α j ∉ Φ) (h_sub : α i - α j ∉ Φ) : P.pairingIn…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma pairing_eq_zero_of_add_notMem_of_sub_notMem (hp : i ≠ j) (hn : α i ≠ -α j)
    (h_add : α i + α j ∉ Φ) (h_sub : α i - α j ∉ Φ) :
    P.pairing i j = 0 := by
  rw [← P.algebraMap_pairingIn ℤ, P.pairingIn_eq_zero_of_add_notMem_of_sub_notMem hp hn h_add h_sub,
    map_zero]

omit [Finite ι] in
/-
**RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule** 是 Mathlib 中的一个引理
，位于命名空间 `RootPairing`。
形式化陈述：root_mem_submodule_iff_of_add_mem_invtSubmodule {K : Type*} [Field K] [NeZ
ero (2 : K)] [Module K M] [Module K N] {P : RootPairing ι K M N} (q : P.invtRoot
Submodule) (hij : P.root i + P.root j in range P.root) : P.root i in (q : Submod
ule K M) ↔ P.root j in (q : Submodule K M)
参数：2 : K；q : P.invtRootSubmodule；hij : P.root i + P.root j in range P.root。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `RootPairing.pairing_eq_zero_iff`：pairing_eq_zero_iff [NeZero (2 : R)] [I
sDomain R] [Module.IsTorsionFree R M] : P.pairing i j = 0 ↔ P.pairing j i = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.root_coroot_eq_pairing`：root_coroot_eq_pairing : P.toLinearM
ap (P.root i) (P.coroot j) = P.pairing i j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用引理 `RootPairing.mem_invtRootSubmodule_iff`：mem_invtRootSubmodule_iff {q : Su
bmodule R M} : q in P.invtRootSubmodule ↔ forall i, q in Module.End.invtSubmodul
e (P.reflection i)
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `Submodule.sub_mem_iff_right`：sub_mem_iff_right (hx : x in p) : x - y in 
p ↔ y in p
· 使用定理 `Submodule.add_mem_iff_right`：∀ {R : Type u} {M : Type v} [inst : Ring R]
 [inst_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   
{x y : M}, x ∈ p …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
-/
lemma root_mem_submodule_iff_of_add_mem_invtSubmodule
    {K : Type*} [Field K] [NeZero (2 : K)] [Module K M] [Module K N] {P : RootPairing ι K M N}
    (q : P.invtRootSubmodule)
    (hij : P.root i + P.root j ∈ range P.root) :
    P.root i ∈ (q : Submodule K M) ↔ P.root j ∈ (q : Submodule K M) := by
  obtain ⟨q, hq⟩ := q
  rw [mem_invtRootSubmodule_iff] at hq
  suffices ∀ i j, P.root i + P.root j ∈ range P.root → P.root i ∈ q → P.root j ∈ q by
    have aux := this j i (by rwa [add_comm]); tauto
  rintro i j ⟨k, hk⟩ hi
  rcases eq_or_ne (P.pairing i j) 0 with hij₀ | hij₀
  · have hik : P.pairing i k ≠ 0 := by
      rw [ne_eq, P.pairing_eq_zero_iff, ← root_coroot_eq_pairing, hk]
      simpa [P.pairing_eq_zero_iff.mp hij₀] using two_ne_zero
    suffices P.root k ∈ q from (q.add_mem_iff_right hi).mp <| hk ▸ this
    replace hq : P.root i - P.pairing i k • P.root k ∈ q := by
      simpa [reflection_apply_root] using hq k hi
    rwa [q.sub_mem_iff_right hi, q.smul_mem_iff hik] at hq
  · replace hq : P.root i - P.pairing i j • P.root j ∈ q := by
      simpa [reflection_apply_root] using hq j hi
    rwa [q.sub_mem_iff_right hi, q.smul_mem_iff hij₀] at hq

namespace InvariantForm

variable [P.IsReduced] (B : P.InvariantForm)
variable {P}

/-
**RootPairing.InvariantForm.apply_eq_or_aux** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng.InvariantForm`。
形式化陈述：apply_eq_or_aux (i j : ι) (h : P.pairingIn Int i j != 0) : B.form (α i) (α
 i) = B.form (α j) (α j) ∨ B.form (α i) (α i) = 2 * B.form (α j) (α j) ∨ B.form 
(α i) (α i) = 3 * B.form (α j) (α j) ∨ B.form (α j) (α j) = 2 * B.form (α i) (α 
i) ∨ B.form (α j) (α j) = 3 * B.form (α i) (α i)
参数：i j : ι；h : P.pairingIn Int i j != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed`：pairingIn
_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] : (P.pairingIn Int i j, P
.pairingIn Int j i) in ({(0, 0), (1, 1), (-1, -1), …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用引理 `RootPairing.InvariantForm.pairing_mul_eq_pairing_mul_swap`：pairing_mul_e
q_pairing_mul_swap : P.pairing j i * B.form (P.root i) (P.root i) = P.pairing i 
j * B.form (P.root j) (P.root j)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
（共 31 条，此处仅展示前 30 条）
-/
lemma apply_eq_or_aux (i j : ι) (h : P.pairingIn ℤ i j ≠ 0) :
    B.form (α i) (α i) = B.form (α j) (α j) ∨
    B.form (α i) (α i) = 2 * B.form (α j) (α j) ∨
    B.form (α i) (α i) = 3 * B.form (α j) (α j) ∨
    B.form (α j) (α j) = 2 * B.form (α i) (α i) ∨
    B.form (α j) (α j) = 3 * B.form (α i) (α i) := by
  have h₁ := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  have h₂ : algebraMap ℤ R (P.pairingIn ℤ j i) * B.form (α i) (α i) =
            algebraMap ℤ R (P.pairingIn ℤ i j) * B.form (α j) (α j) := by
    simpa only [algebraMap_pairingIn] using B.pairing_mul_eq_pairing_mul_swap i j
  aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)

variable [P.IsIrreducible]

/-- Relative of lengths of roots in a reduced irreducible finite crystallographic root pairing are
very constrained. -/
/-
**RootPairing.InvariantForm.apply_eq_or** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.I
nvariantForm`。
形式化陈述：apply_eq_or (i j : ι) : B.form (α i) (α i) = B.form (α j) (α j) ∨ B.form (
α i) (α i) = 2 * B.form (α j) (α j) ∨ B.form (α i) (α i) = 3 * B.form (α j) (α j
) ∨ B.form (α j) (α j) = 2 * B.form (α i) (α i) ∨ B.form (α j) (α j) = 3 * B.for
m (α i) (α i)
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.exists_form_eq_form_and_form_ne_zero`：exists_form_eq_form_an
d_form_ne_zero (B : P.InvariantForm) (i j : ι) : exists k, B.form (P.root k) (P.
root k) = B.form (P.root j) (P.root j)…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RootPairing.InvariantForm.apply_root_root_zero_iff`：apply_root_root_zero
_iff [IsDomain R] [NeZero (2 : R)] : B.form (P.root i) (P.root j) = 0 ↔ P.pairin
g i j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `RootPairing.InvariantForm.apply_eq_or_aux`：apply_eq_or_aux (i j : ι) (h 
: P.pairingIn Int i j != 0) : B.form (α i) (α i) = B.form (α j) (α j) ∨ B.form (
α i) (α i) = 2 * B.form (α j) (…

--- 原说明 ---
Relative of lengths of roots in a reduced irreducible finite crystallographic ro
ot pairing are
very constrained.
-/
lemma apply_eq_or (i j : ι) :
    B.form (α i) (α i) = B.form (α j) (α j) ∨
    B.form (α i) (α i) = 2 * B.form (α j) (α j) ∨
    B.form (α i) (α i) = 3 * B.form (α j) (α j) ∨
    B.form (α j) (α j) = 2 * B.form (α i) (α i) ∨
    B.form (α j) (α j) = 3 * B.form (α i) (α i) := by
  obtain ⟨j', h₁, h₂⟩ := P.exists_form_eq_form_and_form_ne_zero B i j
  suffices P.pairingIn ℤ i j' ≠ 0 by simp only [← h₁, B.apply_eq_or_aux i j' this]
  contrapose h₂
  replace h₂ : P.pairing i j' = 0 := by rw [← P.algebraMap_pairingIn ℤ, h₂, map_zero]
  exact (B.apply_root_root_zero_iff i j').mpr h₂

/-- A reduced irreducible finite crystallographic root system has roots of at most two different
lengths. -/
/-
**RootPairing.InvariantForm.exists_apply_eq_or** 是 Mathlib 中的一个引理，位于命名空间 `RootPa
iring.InvariantForm`。
形式化陈述：exists_apply_eq_or [Nonempty ι] : exists i j, forall k, B.form (α k) (α k)
 = B.form (α i) (α i) ∨ B.form (α k) (α k) = B.form (α j) (α j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `RootPairing.InvariantForm.apply_eq_or`：apply_eq_or (i j : ι) : B.form (α
 i) (α i) = B.form (α j) (α j) ∨ B.form (α i) (α i) = 2 * B.form (α j) (α j) ∨ B
.form (α i) (α i) = 3 * B.f…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
A reduced irreducible finite crystallographic root system has roots of at most t
wo different
lengths.
-/
lemma exists_apply_eq_or [Nonempty ι] : ∃ i j, ∀ k,
    B.form (α k) (α k) = B.form (α i) (α i) ∨
    B.form (α k) (α k) = B.form (α j) (α j) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  by_cases! h : (∀ j, B.form (α j) (α j) = B.form (α i) (α i))
  · refine ⟨i, i, fun j ↦ by simp [h j]⟩
  · obtain ⟨j, hji_ne⟩ := h
    refine ⟨i, j, fun k ↦ ?_⟩
    by_contra! ⟨hki_ne, hkj_ne⟩
    have hij := (B.apply_eq_or i j).resolve_left hji_ne.symm
    have hik := (B.apply_eq_or i k).resolve_left hki_ne.symm
    have hjk := (B.apply_eq_or j k).resolve_left hkj_ne.symm
    grind
/-
**RootPairing.InvariantForm.apply_eq_or_of_apply_ne** 是 Mathlib 中的一个引理，位于命名空间 `R
ootPairing.InvariantForm`。
形式化陈述：apply_eq_or_of_apply_ne (h : B.form (α i) (α i) != B.form (α j) (α j)) (k 
: ι) : B.form (α k) (α k) = B.form (α i) (α i) ∨ B.form (α k) (α k) = B.form (α 
j) (α j)
参数：h : B.form (α i) (α i) != B.form (α j) (α j)；k : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.InvariantForm.exists_apply_eq_or`：exists_apply_eq_or [Nonemp
ty ι] : exists i j, forall k, B.form (α k) (α k) = B.form (α i) (α i) ∨ B.form (
α k) (α k) = B.form (α j) (α j)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma apply_eq_or_of_apply_ne
    (h : B.form (α i) (α i) ≠ B.form (α j) (α j)) (k : ι) :
    B.form (α k) (α k) = B.form (α i) (α i) ∨
    B.form (α k) (α k) = B.form (α j) (α j) := by
  have : Nonempty ι := ⟨i⟩
  obtain ⟨i', j', h'⟩ := B.exists_apply_eq_or
  rcases h' i with hi | hi <;>
  rcases h' j with hj | hj <;>
  specialize h' k <;>
  aesop

end InvariantForm

/-
**RootPairing.forall_pairing_eq_swap_or** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：forall_pairing_eq_swap_or [P.IsReduced] [P.IsIrreducible] : (forall i j, P
.pairing i j = P.pairing j i ∨ P.pairing i j = 2 * P.pairing j i ∨ P.pairing j i
 = 2 * P.pairing i j) ∨ (forall i j, P.pairing i j = P.pairing j i ∨ P.pairing i
 j = 3 * P.pairing j i ∨ P.pairing j i = 3 * P.pairing i j)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.InvariantForm.pairing_mul_eq_pairing_mul_swap`：pairing_mul_e
q_pairing_mul_swap : P.pairing j i * B.form (P.root i) (P.root i) = P.pairing i 
j * B.form (P.root j) (P.root j)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `RootPairing.InvariantForm.ne_zero`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `RootPairing.InvariantForm.apply_eq_or_of_apply_ne`：apply_eq_or_of_apply_
ne (h : B.form (α i) (α i) != B.form (α j) (α j)) (k : ι) : B.form (α k) (α k) =
 B.form (α i) (α i) ∨ B.form (α k) (α k…
· 使用引理 `RootPairing.InvariantForm.apply_eq_or`：apply_eq_or (i j : ι) : B.form (α
 i) (α i) = B.form (α j) (α j) ∨ B.form (α i) (α i) = 2 * B.form (α j) (α j) ∨ B
.form (α i) (α i) = 3 * B.f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma forall_pairing_eq_swap_or [P.IsReduced] [P.IsIrreducible] :
    (∀ i j, P.pairing i j = P.pairing j i ∨
            P.pairing i j = 2 * P.pairing j i ∨
            P.pairing j i = 2 * P.pairing i j) ∨
    (∀ i j, P.pairing i j = P.pairing j i ∨
            P.pairing i j = 3 * P.pairing j i ∨
            P.pairing j i = 3 * P.pairing i j) := by
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  by_cases! h : ∀ i j, B.form (α i) (α i) = B.form (α j) (α j)
  · refine Or.inl fun i j ↦ Or.inl ?_
    have := B.pairing_mul_eq_pairing_mul_swap j i
    rwa [h i j, mul_left_inj' (B.ne_zero j)] at this
  obtain ⟨i, j, hij⟩ := h
  have key := B.apply_eq_or_of_apply_ne hij
  set li := B.form (α i) (α i)
  set lj := B.form (α j) (α j)
  have : (li = 2 * lj ∨ lj = 2 * li) ∨ (li = 3 * lj ∨ lj = 3 * li) := by
    have := B.apply_eq_or i j; tauto
  rcases this with this | this
  · refine Or.inl fun k₁ k₂ ↦ ?_
    have hk := B.pairing_mul_eq_pairing_mul_swap k₁ k₂
    rcases this with h₀ | h₀ <;> rcases key k₁ with h₁ | h₁ <;> rcases key k₂ with h₂ | h₂ <;>
    simp only [h₁, h₂, h₀, ← mul_assoc, mul_comm, mul_eq_mul_right_iff] at hk <;>
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
  · refine Or.inr fun k₁ k₂ ↦ ?_
    have hk := B.pairing_mul_eq_pairing_mul_swap k₁ k₂
    rcases this with h₀ | h₀ <;> rcases key k₁ with h₁ | h₁ <;> rcases key k₂ with h₂ | h₂ <;>
    simp only [h₁, h₂, h₀, ← mul_assoc, mul_comm, mul_eq_mul_right_iff] at hk <;>
    aesop -- https://github.com/leanprover-community/mathlib4/issues/24551 (this should be faster)
/-
**RootPairing.forall_pairingIn_eq_swap_or** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
`。
形式化陈述：forall_pairingIn_eq_swap_or [P.IsReduced] [P.IsIrreducible] : (forall i j,
 P.pairingIn Int i j = P.pairingIn Int j i ∨ P.pairingIn Int i j = 2 * P.pairing
In Int j i ∨ P.pairingIn Int j i = 2 * P.pairingIn Int i j) ∨ (forall i j, P.pai
ringIn Int i j = P.pairingIn Int j i ∨ P.pairingIn Int i j = 3 * P.pairingIn Int
 j i ∨ P.pairingIn Int j i = 3 * P.pairingIn Int i j)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用引理 `RootPairing.forall_pairing_eq_swap_or`：forall_pairing_eq_swap_or [P.IsRe
duced] [P.IsIrreducible] : (forall i j, P.pairing i j = P.pairing j i ∨ P.pairin
g i j = 2 * P.pairing j i ∨…
-/
lemma forall_pairingIn_eq_swap_or [P.IsReduced] [P.IsIrreducible] :
    (∀ i j, P.pairingIn ℤ i j = P.pairingIn ℤ j i ∨
            P.pairingIn ℤ i j = 2 * P.pairingIn ℤ j i ∨
            P.pairingIn ℤ j i = 2 * P.pairingIn ℤ i j) ∨
    (∀ i j, P.pairingIn ℤ i j = P.pairingIn ℤ j i ∨
            P.pairingIn ℤ i j = 3 * P.pairingIn ℤ j i ∨
            P.pairingIn ℤ j i = 3 * P.pairingIn ℤ i j) := by
  simpa only [← P.algebraMap_pairingIn ℤ, eq_intCast, ← Int.cast_mul, Int.cast_inj,
    ← map_ofNat (algebraMap ℤ R)] using P.forall_pairing_eq_swap_or

end RootPairing

