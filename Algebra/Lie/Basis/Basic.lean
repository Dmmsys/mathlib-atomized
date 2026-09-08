/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.Weights.Cartan

/-!
# Bases of semisimple Lie algebras

In this file we define bases of semisimple Lie algebras. Given an indexing type `ι`, a basis of a
Lie algebra consists of a non-degenerate matrix of integers `A` indexed by `ι × ι` and generators
`h i`, `e i`, `f i` indexed by `ι`, each forming an `sl₂` triple, and satisfying the Chevalley-Serre
relations:
* `⁅h i, h j⁆ = 0`
* `⁅h j, e i⁆ =  A i j • e i`
* `⁅h j, f i⁆ = -A i j • f i`
* `⁅e i, f j⁆ = 0` (for `i ≠ j`)

This concept appears not to have a name in the informal literature and so we call it simply a basis.
With further axioms (constraining the structure constants which appear in products of the form
`⁅e i, e j⁆`, `⁅f i, f j⁆`) one obtains the concept of a Weyl or Chevalley basis.
See e.g., [serre1965](Ch. V, §4, §6).

## Main definitions / results:

* `LieAlgebra.Basis`: the concept of a basis for a Lie algebra.
* `LieAlgebra.Basis.cartanMatrix_base_eq`: the matrix of a `LieAlgebra.Basis` is the Cartan matrix
  of the associated based root system.

## TODO

* Show that every semisimple Lie algebra has a basis.
* Define Weyl, Chevalley bases.

-/

@[expose] public section

open Function LieSubalgebra Module Set

noncomputable section

namespace LieAlgebra

/-- A basis for a semisimple Lie algebra distinguishes a natural Cartan subalgebra and a base
for the associated root system. -/
@[ext]
/-
**LieAlgebra.Basis** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：(ι : Type u_1) →   {R : Type u_2} →     {L : Type u_3} →       [Finite ι] 
→         [inst : CommRing R] → [inst_1 : LieRing L] → [inst_2 : LieAlgebra R L]
 → LieSubalgebra R L → Type (max u_1 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A basis for a semisimple Lie algebra distinguishes a natural Cartan subalgebra a
nd a base
for the associated root system.
-/
structure Basis (ι : Type*) {R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L]
    (H : LieSubalgebra R L) where
  /-- The Cartan matrix. -/
  A : Matrix ι ι ℤ
  /-- The basis for the Cartan subalgebra. -/
  h : ι → L
  /-- The generators of the upper Borel subalgebra. -/
  e : ι → L
  /-- The generators of the lower Borel subalgebra. -/
  f : ι → L
  cartan_eq_lieSpan : H = lieSpan R L (range h)
  span_ef : lieSpan R L (range e ∪ range f) = ⊤
  linInd : LinearIndependent R h
  nondegen : A.Nondegenerate -- TODO Replace with `(b.A.det : R) ≠ 0` to support positive char
  sl2 (i : ι) : IsSl2Triple (h i) (e i) (f i)
  lie_h_h (i j : ι) : ⁅h i, h j⁆ = 0
  lie_h_e (i j : ι) : ⁅h j, e i⁆ = A i j • e i
  lie_h_f (i j : ι) : ⁅h j, f i⁆ = -A i j • f i
  lie_e_f_ne (i j : ι) (hij : i ≠ j) : ⁅e i, f j⁆ = 0

namespace Basis

section CommRing

variable {ι R L : Type*} [Finite ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L} (b : Basis ι H)

/-
**LieAlgebra.Basis.A_diag_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [inst : Finite ι] [inst_1 :
 CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H : LieSubalgebra
 R L} (b : LieAlgebra.Basis ι H) [IsAddTorsionFree L] (i : ι), b.A i i = 2
参数：b : LieAlgebra.Basis ι H；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ofNat_smul_eq_nsmul`：ofNat_smul_eq_nsmul (n : Nat) [n.AtLeastTwo] (b : M
) : (ofNat(n) : R) • b = ofNat(n) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSl2Triple.lie_h_e_nsmul`：∀ {L : Type u_2} [inst : LieRing L] {h e f : 
L}, IsSl2Triple h e f → ⁅h, e⁆ = 2 • e
· 使用定理 `LieAlgebra.Basis.sl2`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [in
st : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra
 R L] {H :…
· 使用定理 `LieAlgebra.Basis.lie_h_e`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3}
 [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlg
ebra R L] {H :…
· 使用定理 `_private.Mathlib.Algebra.Lie.Basis.Basic.0.LieAlgebra.Basis.A_diag_eq_tw
o._abel_1_1`：∀ {ι : Type u_2} {R : Type u_3} {L : Type u_1} [inst : Finite ι] [i
nst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H :…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `IsAddTorsionFree.zsmul_eq_zero_iff_left`：∀ {G : Type u_2} [inst : AddGro
up G] [IsAddTorsionFree G] {n : ℤ} {a : G}, a ≠ 0 → (n • a = 0 ↔ n = 0)
· 使用引理 `IsSl2Triple.e_ne_zero`：e_ne_zero (t : IsSl2Triple h e f) : e != 0
-/
@[simp] lemma A_diag_eq_two [IsAddTorsionFree L] (i : ι) : b.A i i = 2 := by
  have : NoZeroSMulDivisors ℤ L := IsAddTorsionFree.to_noZeroSMulDivisors_int
  have aux : (b.A i i - 2) • b.e i = 0 := by
    rw [sub_smul, ofNat_smul_eq_nsmul, ← (b.sl2 i).lie_h_e_nsmul, b.lie_h_e i i]; abel
  rwa [IsAddTorsionFree.zsmul_eq_zero_iff_left (b.sl2 i).e_ne_zero, sub_eq_zero] at aux
/-
**LieAlgebra.Basis.coe_cartan_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Basi
s`。
形式化陈述：coe_cartan_eq_span : H = Submodule.span R (range b.h)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.Basis.cartan_eq_lieSpan`：∀ {ι : Type u_1} {R : Type u_2} {L :
 Type u_3} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_
3 : LieAlgebra R L] {H :…
· 使用定理 `LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero`：coe_lieSpan_eq_
span_of_forall_lie_eq_zero {s : Set L} (hs : forallᵉ (x in s) (y in s), ⁅x, y⁆ =
 0) : lieSpan R L s = span R s
· 使用定理 `LieAlgebra.Basis.lie_h_h`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3}
 [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlg
ebra R L] {H :…
-/
lemma coe_cartan_eq_span :
    H = Submodule.span R (range b.h) := by
  conv_lhs => rw [b.cartan_eq_lieSpan]
  apply coe_lieSpan_eq_span_of_forall_lie_eq_zero
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact b.lie_h_h i j

include b in
/-
**LieAlgebra.Basis.isLieAbelian_cartan** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Bas
is`。
形式化陈述：isLieAbelian_cartan : IsLieAbelian H
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.Basis.cartan_eq_lieSpan`：∀ {ι : Type u_1} {R : Type u_2} {L :
 Type u_3} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_
3 : LieAlgebra R L] {H :…
· 使用定理 `LieSubalgebra.isLieAbelian_lieSpan_iff`：∀ {R : Type u_1} {L : Type u_2} 
[inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] {s : Set L}, 
  IsLieAbelian ↥(LieSubalgeb…
· 使用定理 `LieAlgebra.Basis.lie_h_h`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3}
 [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlg
ebra R L] {H :…
-/
theorem isLieAbelian_cartan : IsLieAbelian H := by
  rw [b.cartan_eq_lieSpan, isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact b.lie_h_h i j

/-- A basis has a natural involution obtained by interchanging the roles of `e` and `f` and
negating `h`. -/
/-
**LieAlgebra.Basis.symm** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {L : Type u_3} →       [inst : Fin
ite ι] →         [inst_1 : CommRing R] →           [inst_2 : LieRing L] →       
      [inst_3 : LieAlgebra R L] → {H : LieSubalgebra R L} → LieAlgebra.Basis ι H
 → LieAlgebra.Basis ι H
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.Basis.nondegen`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3
} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAl
gebra R L] {H :…

--- 原说明 ---
A basis has a natural involution obtained by interchanging the roles of `e` and 
`f` and
negating `h`.
-/
@[simps -fullyApplied] def symm : Basis ι H where
  A := b.A
  h := -b.h
  e := b.f
  f := b.e
  cartan_eq_lieSpan := by
    rw [← neg_range', lieSpan_neg]
    exact b.cartan_eq_lieSpan
  nondegen := b.nondegen
  linInd := b.linInd.neg
  sl2 i := (b.sl2 i).symm
  lie_h_h i j := by rw [Pi.neg_apply, Pi.neg_apply, neg_lie, lie_neg, b.lie_h_h i j, neg_neg]
  lie_h_e i j := by rw [Pi.neg_apply, neg_lie, b.lie_h_f i j, neg_smul, neg_neg]
  lie_h_f i j := by rw [Pi.neg_apply, neg_lie, b.lie_h_e, neg_smul]
  lie_e_f_ne i j h := by rw [← lie_skew, neg_eq_zero, b.lie_e_f_ne j i h.symm]
  span_ef := by rw [union_comm, b.span_ef]
/-
**LieAlgebra.Basis.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [inst : Finite ι] [inst_1 :
 CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H : LieSubalgebra
 R L} (b : LieAlgebra.Basis ι H), b.symm.symm = b
参数：b : LieAlgebra.Basis ι H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.Basis.ext`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} {in
st : Finite ι} {inst_1 : CommRing R} {inst_2 : LieRing L}   {inst_3 : LieAlgebra
 R L} {H :…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.Basis.symm_A`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} 
[inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlge
bra R L] {H :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieAlgebra.Basis.symm_h`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} 
[inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlge
bra R L] {H :…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `LieAlgebra.Basis.symm_e`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} 
[inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlge
bra R L] {H :…
· 使用定理 `LieAlgebra.Basis.symm_f`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} 
[inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlge
bra R L] {H :…
-/
@[simp] lemma symm_symm : b.symm.symm = b := by aesop

/-- As shown in `LieAlgebra.Basis.coroot_eq_h'` this is a coroot. -/
/-
**LieAlgebra.Basis.h'** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：h' (i : ι) : H
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As shown in `LieAlgebra.Basis.coroot_eq_h'` this is a coroot.
-/
def h' (i : ι) : H := ⟨b.h i, b.cartan_eq_lieSpan ▸ subset_lieSpan <| mem_range_self i⟩
/-
**LieAlgebra.Basis.symm_h'** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [inst : Finite ι] [inst_1 :
 CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H : LieSubalgebra
 R L} (b : LieAlgebra.Basis ι H) (i : ι), b.symm.h' i = -b.h' i
参数：b : LieAlgebra.Basis ι H；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_h' (i : ι) : (b.symm.h' i) = -b.h' i := rfl
/-
**LieAlgebra.Basis.cartan_lie_mem_lieSpan_e** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebr
a.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma cartan_lie_mem_lieSpan_e {x y : L}
    (hx : x ∈ H) (hy : y ∈ lieSpan R L (range b.e)) :
    ⁅x, y⁆ ∈ lieSpan R L (range b.e) := by
  induction hy using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    rw [← mem_toSubmodule, b.coe_cartan_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      rw [b.lie_h_e]
      apply zsmul_mem <| subset_lieSpan <| mem_range_self i
    | zero => simp
    | add v w _ _ hv hw => simpa using add_mem hv hw
    | smul t v _ hv => simpa using LieSubalgebra.smul_mem _ t hv
  | zero => simp
  | add u v _ _ hu hv => simpa using add_mem hu hv
  | smul t u _ hu => simpa using LieSubalgebra.smul_mem _ t hu
  | lie u v hu hv hu' hv' =>
    rw [leibniz_lie, ← lie_skew _ v, neg_add_eq_sub]
    exact sub_mem (LieSubalgebra.lie_mem _ hu hv') (LieSubalgebra.lie_mem _ hv hu')

/-- The nilpotent part of the "upper" Borel subalgebra associated to a basis. -/
/-
**LieAlgebra.Basis.borelUpper** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：borelUpper : LieSubmodule R H L where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nilpotent part of the "upper" Borel subalgebra associated to a basis.
-/
def borelUpper : LieSubmodule R H L where
  __ := lieSpan R L <| range b.e
  lie_mem {x y} hy := by
    obtain ⟨x, hx⟩ := x
    simpa using b.cartan_lie_mem_lieSpan_e hx hy

/-- The nilpotent part of the "lower" Borel subalgebra associated to a basis. -/
/-
**LieAlgebra.Basis.borelLower** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：borelLower : LieSubmodule R H L where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nilpotent part of the "lower" Borel subalgebra associated to a basis.
-/
def borelLower : LieSubmodule R H L where
  __ := lieSpan R L <| range b.f
  lie_mem := b.symm.borelUpper.lie_mem
/-
**LieAlgebra.Basis.iSup_cartan_borelLower_borelUpper_eq_top_aux** 是 Mathlib 中的一个
引理，位于命名空间 `LieAlgebra.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma iSup_cartan_borelLower_borelUpper_eq_top_aux
    {y z : L} (hy : y ∈ lieSpan R L (range b.e)) (hz : z ∈ lieSpan R L (range b.f)) :
    ⁅y, z⁆ ∈ H.toLieSubmodule ⊔ b.borelLower ⊔ b.borelUpper := by
  have (i : ι) (x : L) (hx : x ∈ lieSpan R L (range b.f)) :
      ⁅b.e i, x⁆ ∈ H.toLieSubmodule ⊔ b.borelLower := by
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem u hu =>
      obtain ⟨j, rfl⟩ := hu
      rcases eq_or_ne i j with rfl | hij
      · rw [(b.sl2 i).lie_e_f]
        apply LieSubmodule.mem_sup_left
        nth_rw 1 [mem_toLieSubmodule, b.cartan_eq_lieSpan]
        exact LieSubalgebra.subset_lieSpan <| mem_range_self i
      · simp [b.lie_e_f_ne _ _ hij]
    | zero => simp
    | add u v _ _ hu hv => rw [lie_add]; exact add_mem hu hv
    | smul t u _ hu => rw [lie_smul]; exact SMulMemClass.smul_mem t hu
    | lie u v hu hv hu' hv' =>
      obtain ⟨w₁, hw₁, w₂, hw₂, hwu⟩ : ∃ y ∈ H, ∃ z ∈ b.borelLower, y + z = ⁅b.e i, u⁆ := by
        simpa only [LieSubmodule.mem_sup] using! hu'
      obtain ⟨w₃, hw₃, w₄, hw₄, hwv⟩ : ∃ y ∈ H, ∃ z ∈ b.borelLower, y + z = ⁅b.e i, v⁆ := by
        simpa only [LieSubmodule.mem_sup] using! hv'
      rw [leibniz_lie, ← hwu, ← hwv, lie_add, add_lie, ← add_assoc]
      repeat apply add_mem
      · exact LieSubmodule.mem_sup_right <| b.borelLower.lie_mem (x := ⟨w₁, hw₁⟩) hv
      · exact LieSubmodule.mem_sup_right <| LieSubalgebra.lie_mem _ hw₂ hv
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| b.borelLower.lie_mem (x := ⟨w₃, hw₃⟩) hu
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| LieSubalgebra.lie_mem _ hw₄ hu
  induction hy using lieSpan_induction generalizing z with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact LieSubmodule.mem_sup_left <| this i z hz
  | zero => simp
  | add u v _ _ hu hv => rw [add_lie]; exact add_mem (hu hz) (hv hz)
  | smul t u _ hu => rw [smul_lie]; exact SMulMemClass.smul_mem t (hu hz)
  | lie u v hu hv hu' hv' =>
    rw [lie_lie]
    apply sub_mem
    · obtain ⟨yc, hyc, yl, hyl, yu, hyu, aux⟩ :
        ∃ᵉ (yc ∈ H) (yl ∈ lieSpan R L (range b.f)) (yu ∈ lieSpan R L (range b.e)),
        yc + yl + yu = ⁅v, z⁆ := by simpa [LieSubmodule.mem_sup] using! hv' hz
      simp only [← aux, lie_add]
      repeat apply add_mem
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hu
      · exact hu' hyl
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| LieSubalgebra.lie_mem _ hyu hu
    · obtain ⟨yc, hyc, yl, hyl, yu, hyu, aux⟩ :
        ∃ᵉ (yc ∈ H) (yl ∈ lieSpan R L (range b.f)) (yu ∈ lieSpan R L (range b.e)),
        yc + yl + yu = ⁅u, z⁆ := by simpa [LieSubmodule.mem_sup] using! hu' hz
      simp only [← aux, lie_add]
      repeat apply add_mem
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hv
      · exact hv' hyl
      · rw [← lie_skew, neg_mem_iff]
        exact LieSubmodule.mem_sup_right <| LieSubalgebra.lie_mem _ hyu hv

/-- Lemma 4.5 from [Geck](Geck2017). -/
/-
**LieAlgebra.Basis.iSup_cartan_borelLower_borelUpper_eq_top** 是 Mathlib 中的一个引理，位
于命名空间 `LieAlgebra.Basis`。
形式化陈述：iSup_cartan_borelLower_borelUpper_eq_top : iSup ![H.toLieSubmodule, b.bore
lLower, b.borelUpper] = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.Basis.span_ef`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3}
 [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlg
ebra R L] {H :…
· 使用定理 `LieSubalgebra.lieSpan_induction`：lieSpan_induction {p : (x : L) -> x in 
lieSpan R L s -> Prop} (mem : forall (x) (h : x in s), p x (subset_lieSpan h)) (
zero : p 0 (LieSubalg…
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `LieSubmodule.mem_sup_right`：mem_sup_right {x : M} (hx : x in N') : x in 
N ⊔ N'
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `LieSubmodule.mem_sup_left`：mem_sup_left {x : M} (hx : x in N) : x in N ⊔
 N'
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `LieSubalgebra.lie_mem`：lie_mem {x y : L} (hx : x in L') (hy : y in L') :
 (⁅x, y⁆ : L) in L'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `_private.Mathlib.Algebra.Lie.Basis.Basic.0.LieAlgebra.Basis.iSup_cartan_
borelLower_borelUpper_eq_top_aux`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3}
 [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlg
ebra R L] {H :…
· 使用引理 `iSup_fin_three`：iSup_fin_three {α : Type*} [CompleteLattice α] {f : Fin 
3 -> α} : ⨆ i, f i = f 0 ⊔ f 1 ⊔ f 2

--- 原说明 ---
Lemma 4.5 from [Geck](Geck2017).
-/
lemma iSup_cartan_borelLower_borelUpper_eq_top :
    iSup ![H.toLieSubmodule, b.borelLower, b.borelUpper] = ⊤ := by
  suffices H.toLieSubmodule ⊔ b.borelLower ⊔ b.borelUpper = ⊤ by simpa
  refine eq_top_iff.mpr fun x hx ↦ ?_
  replace hx : x ∈ lieSpan R L (range b.e ∪ range b.f) := by simp [b.span_ef]
  induction hx using lieSpan_induction with
  | mem u hu =>
    rcases (mem_union _ _ _).mpr hu with hu | hu
    · exact LieSubmodule.mem_sup_right <| subset_lieSpan hu
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <| subset_lieSpan hu
  | zero => simp
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul t u _ hu => exact SMulMemClass.smul_mem t hu
  | lie u v _ _ hu hv =>
    obtain ⟨yc, hyc, yl, hyl, yu, hyu, rfl⟩ :
        ∃ᵉ (yc ∈ H) (yl ∈ lieSpan R L (range b.f)) (yu ∈ lieSpan R L (range b.e)),
          yc + yl + yu = u := by simpa [LieSubmodule.mem_sup] using! hu
    obtain ⟨zc, hzc, zl, hzl, zu, hzu, rfl⟩ :
        ∃ᵉ (zc ∈ H) (zl ∈ lieSpan R L (range b.f)) (zu ∈ lieSpan R L (range b.e)),
          zc + zl + zu = v := by simpa [LieSubmodule.mem_sup] using! hv
    simp only [lie_add, add_lie, ← add_assoc]
    repeat apply add_mem
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_left <| lie_mem _ hyc hzc
    · rw [← lie_skew, neg_mem_iff]
      exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <|
        b.borelLower.lie_mem (x := ⟨zc, hzc⟩) hyl
    · rw [← lie_skew, neg_mem_iff]
      exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨zc, hzc⟩) hyu
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <|
        b.borelLower.lie_mem (x := ⟨yc, hyc⟩) hzl
    · exact LieSubmodule.mem_sup_left <| LieSubmodule.mem_sup_right <| lie_mem _ hyl hzl
    · exact b.iSup_cartan_borelLower_borelUpper_eq_top_aux hyu hzl
    · exact LieSubmodule.mem_sup_right <| b.borelUpper.lie_mem (x := ⟨yc, hyc⟩) hzu
    · rw [← lie_skew, neg_mem_iff]
      exact b.iSup_cartan_borelLower_borelUpper_eq_top_aux hzu hyl
    · exact LieSubmodule.mem_sup_right <| lie_mem _ hyu hzu

variable [Fintype ι]

/-- These elements constitute a base for the root system of the Lie algebra relative to the
associated Cartan subalgebra. -/
/-
**LieAlgebra.Basis.baseSupp** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：baseSupp (i : ι) : Dual R H
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.Basis.linInd`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} 
[inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlge
bra R L] {H :…
· 使用引理 `LieAlgebra.Basis.coe_cartan_eq_span`：coe_cartan_eq_span : H = Submodule.
span R (range b.h)

--- 原说明 ---
These elements constitute a base for the root system of the Lie algebra relative
 to the
associated Cartan subalgebra.
-/
def baseSupp (i : ι) : Dual R H :=
  ∑ j, b.A i j •
    ((Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm).coord j
/-
**LieAlgebra.Basis.baseSupp_apply_h'** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Basis
`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [inst : Finite ι] [inst_1 :
 CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H : LieSubalgebra
 R L} (b : LieAlgebra.Basis ι H) [inst_4 : Fintype ι] (i j : ι),   (b.baseSupp i
) (b.h' j) = ↑(b.A i j)
参数：b : LieAlgebra.Basis ι H；i j : ι；b.baseSupp i；b.h' j；b.A i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.Basis.linInd`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} 
[inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlge
bra R L] {H :…
· 使用引理 `LieAlgebra.Basis.coe_cartan_eq_span`：coe_cartan_eq_span : H = Submodule.
span R (range b.h)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Module.Basis.span_repr_eq_single`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] {v : ι → M} (hl…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
@[simp] lemma baseSupp_apply_h' (i j : ι) :
    b.baseSupp i (b.h' j) = b.A i j := by
  classical
  simp only [baseSupp, LinearMap.coe_sum, Finset.sum_apply]
  let e := LinearEquiv.ofEq _ _ b.coe_cartan_eq_span
  let f (k : ι) : R := b.A i k • (Basis.span b.linInd).repr (e <| b.h' j) k
  change ∑ k, f k = _
  have : f = fun k ↦ if j = k then (b.A i k : R) else 0 := by
    have : (Basis.span b.linInd).repr (e <| b.h' j) = .single j 1 := Basis.span_repr_eq_single _ _
    ext k
    simp [f, this, Finsupp.single_apply]
  simp [this]

set_option backward.isDefEq.respectTransparency.types false in
/-
**LieAlgebra.Basis.symm_baseSupp** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [inst : Finite ι] [inst_1 :
 CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H : LieSubalgebra
 R L} (b : LieAlgebra.Basis ι H) [inst_4 : Fintype ι],   b.symm.baseSupp = -b.ba
seSupp
参数：b : LieAlgebra.Basis ι H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.Basis.linInd`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} 
[inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlge
bra R L] {H :…
· 使用引理 `LieAlgebra.Basis.coe_cartan_eq_span`：coe_cartan_eq_span : H = Submodule.
span R (range b.h)
· 使用定理 `LinearIndependent.neg`：LinearIndependent.neg (hv : LinearIndependent R v
) : LinearIndependent R (-v)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_neg`：span_neg (s : Set M) : span R (-s) = span R s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Module.Basis.span_neg`：span_neg {R M : Type*} [Ring R] [AddCommGroup M] 
[Module R M] {v : ι -> M} (hli : LinearIndependent R v) (h : span R (range v) = 
span R (ran…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
-/
@[simp] lemma symm_baseSupp :
    b.symm.baseSupp = -b.baseSupp := by
  let b₁ : Module.Basis ι R H :=
    (Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm
  let b₂ : Module.Basis ι R H :=
    (Basis.span b.linInd.neg).map (LinearEquiv.ofEq _ _ b.symm.coe_cartan_eq_span).symm
  suffices b₁.coord = -b₂.coord by
    ext1 i
    change ∑ j, b.A i j • b₂.coord j = - ∑ j, b.A i j • b₁.coord j
    simp [this]
  simp only [b₁, b₂, Basis.span_neg b.linInd]
  aesop
/-
**LieAlgebra.Basis.linearIndependent_baseSupp** 是 Mathlib 中的一个引理，位于命名空间 `LieAlge
bra.Basis`。
形式化陈述：linearIndependent_baseSupp [IsDomain R] [CharZero R] : LinearIndependent R
 b.baseSupp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.nondegenerate_iff_det_ne_zero`：nondegenerate_iff_det_ne_zero [Dec
idableEq n] : Nondegenerate M ↔ M.det != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Matrix.Nondegenerate.det_ne_zero`：∀ {n : Type u_1} [inst : Fintype n] {A
 : Type u_4} [inst_1 : CommRing A] [IsDomain A] {M : Matrix n n A}   [inst_3 : D
ecidableEq n], M.Nonde…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `LieAlgebra.Basis.nondegen`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3
} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAl
gebra R L] {H :…
· 使用定理 `LieAlgebra.Basis.linInd`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} 
[inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlge
bra R L] {H :…
· 使用引理 `LieAlgebra.Basis.coe_cartan_eq_span`：coe_cartan_eq_span : H = Submodule.
span R (range b.h)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Basis.linearIndependent_coord`：linearIndependent_coord {R : Type*
} [CommSemiring R] [Module R M] (b : Basis ι R M) : LinearIndependent R b.coord
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用引理 `LinearIndependent.sum_smul_of_nondegenerate`：LinearIndependent.sum_smul_
of_nondegenerate {ι κ R M : Type*} [Fintype ι] [Finite κ] [CommRing R] [AddCommG
roup M] [Module R M] {v : ι -> M}…
-/
lemma linearIndependent_baseSupp [IsDomain R] [CharZero R] :
    LinearIndependent R b.baseSupp := by
  classical
  have : ((Int.castRingHom R).mapMatrix b.A).Nondegenerate := by
    rw [Matrix.nondegenerate_iff_det_ne_zero, ← RingHom.map_det]
    simpa using! b.nondegen.det_ne_zero
  let v : ι → Dual R H :=
    ((Basis.span b.linInd).map (LinearEquiv.ofEq _ _ b.coe_cartan_eq_span).symm).coord
  have hv : LinearIndependent R v := Basis.linearIndependent_coord _
  simpa [Int.cast_smul_eq_zsmul] using! hv.sum_smul_of_nondegenerate this
/-
**LieAlgebra.Basis.baseSupp_apply_smul_e** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.B
asis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [inst : Finite ι] [inst_1 :
 CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H : LieSubalgebra
 R L} (b : LieAlgebra.Basis ι H) [inst_4 : Fintype ι] (i : ι) (x : ↥H),   (b.bas
eSupp i) x • b.e i = ⁅x, b.e i⁆
参数：b : LieAlgebra.Basis ι H；i : ι；x : ↥H；b.baseSupp i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.Basis.coe_cartan_eq_span`：coe_cartan_eq_span : H = Submodule.
span R (range b.h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.mem_toSubmodule`：mem_toSubmodule {x : L} : x in (L' : Subm
odule R L) ↔ x in L'
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieAlgebra.Basis.baseSupp_apply_h'`：∀ {ι : Type u_1} {R : Type u_2} {L :
 Type u_3} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_
3 : LieAlgebra R L] {H :…
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `LieAlgebra.Basis.lie_h_e`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3}
 [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlg
ebra R L] {H :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
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
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddMemClass.mk_add_mk`：∀ {M : Type u_1} {A : Type u_3} [inst : Add M] [i
nst_1 : SetLike A M] [hA : AddMemClass A M] (S' : A) (x y : M)   (hx : x ∈ S') (
hy : y ∈ S'…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `LieSubalgebra.instSMulMemClass`：∀ (R : Type u) (L : Type v) [inst : Comm
Ring R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   SMulMemClass (LieSubal
gebra R L) R L
（共 36 条，此处仅展示前 30 条）
-/
@[simp] lemma baseSupp_apply_smul_e (i : ι) (x : H) :
    b.baseSupp i x • b.e i = ⁅x, b.e i⁆ := by
  obtain ⟨x, hx⟩ := x
  simp only [coe_bracket_of_module]
  have hx' : x ∈ Submodule.span R (range b.h) := by
    rwa [← LieSubalgebra.mem_toSubmodule, b.coe_cartan_eq_span] at hx
  induction hx' using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j, rfl⟩ := hu
    change b.baseSupp i (b.h' j) • _ = _
    simp [b.lie_h_e, Int.cast_smul_eq_zsmul]
  | zero => change b.baseSupp i 0 • _ = _; simp
  | add u v hu hv hu' hv' =>
    rw [← coe_cartan_eq_span, LieSubalgebra.mem_toSubmodule] at hu hv
    rw [← AddMemClass.mk_add_mk _ u v hu hv]
    simp only [map_add, add_smul, add_lie] at hu' hv' ⊢
    rw [hu', hv']
  | smul t u hu hv' =>
    rw [← coe_cartan_eq_span, LieSubalgebra.mem_toSubmodule] at hu
    rw [← SetLike.mk_smul_mk _ t u hu, map_smul, smul_assoc, hv', smul_lie]
/-
**LieAlgebra.Basis.baseSupp_apply_smul_f** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.B
asis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [inst : Finite ι] [inst_1 :
 CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H : LieSubalgebra
 R L} (b : LieAlgebra.Basis ι H) [inst_4 : Fintype ι] (i : ι) (x : ↥H),   (b.bas
eSupp i) x • b.f i = -⁅x, b.f i⁆
参数：b : LieAlgebra.Basis ι H；i : ι；x : ↥H；b.baseSupp i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `LinearMap.neg_apply`：neg_apply (f : M ->ₛₗ[σ₁₂] N₂) (x : M) : (-f) x = -
f x
· 使用定理 `LieAlgebra.Basis.baseSupp_apply_smul_e`：∀ {ι : Type u_1} {R : Type u_2} 
{L : Type u_3} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [i
nst_3 : LieAlgebra R L] {H :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieAlgebra.Basis.symm_baseSupp`：∀ {ι : Type u_1} {R : Type u_2} {L : Typ
e u_3} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : 
LieAlgebra R L] {H :…
· 使用定理 `LieAlgebra.Basis.symm_e`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} 
[inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlge
bra R L] {H :…
-/
@[simp] lemma baseSupp_apply_smul_f (i : ι) (x : H) :
    b.baseSupp i x • b.f i = -⁅x, b.f i⁆ := by
  rw [← neg_eq_iff_eq_neg, ← neg_smul, ← LinearMap.neg_apply]
  have := b.symm.baseSupp_apply_smul_e i x
  simp only [symm_baseSupp, Pi.neg_apply, symm_e] at this
  exact this

variable [IsDomain R] [CharZero R]

set_option backward.isDefEq.respectTransparency.types false in
/-- Lemma 4.4 from [Geck](Geck2017). -/
/-
**LieAlgebra.Basis.borelUpper_le_biSup** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Bas
is`。
形式化陈述：borelUpper_le_biSup : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `LieAlgebra.Basis.isLieAbelian_cartan`：isLieAbelian_cartan : IsLieAbelian
 H
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieSubalgebra.lieSpan_induction`：lieSpan_induction {p : (x : L) -> x in 
lieSpan R L s -> Prop} (mem : forall (x) (h : x in s), p x (subset_lieSpan h)) (
zero : p 0 (LieSubalg…
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `LieSubmodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι} {b : M} {N : ι -> LieS
ubmodule R L M} (i : ι) (h : b in N i) : b in ⨆ i, N i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LieAlgebra.rootSpace.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [inst :
 CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra
 R L) [inst_3 : LieRi…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
Lemma 4.4 from [Geck](Geck2017).
-/
lemma borelUpper_le_biSup :
    letI := b.isLieAbelian_cartan
    b.borelUpper ≤ ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • b.baseSupp i) := by
  let := b.isLieAbelian_cartan
  classical
  intro x hx
  replace hx : x ∈ lieSpan R L (range b.e) := by simpa [borelUpper] using hx
  induction hx using lieSpan_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    apply LieSubmodule.mem_iSup_of_mem (Pi.single i 1)
    simp only [ne_eq, Pi.single_eq_zero_iff, one_ne_zero, not_false_eq_true, nsmul_eq_mul, iSup_pos,
      LieModule.mem_genWeightSpace, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply,
      Subtype.forall, toEnd_mk]
    exact fun y hy ↦ ⟨1, by simp [Pi.single_apply]⟩
  | zero => simp
  | add _ _ _ _ hu hv => exact add_mem hu hv
  | smul t _ _ hu => exact SMulMemClass.smul_mem t hu
  | lie u v _ _ hu hv =>
    let s : Set (H → R) := {χ | ∃ n : ι → ℕ, n ≠ 0 ∧ χ = ∑ i, n i • b.baseSupp i}
    have hs : ∀ χ₁ ∈ s, ∀ χ₂ ∈ s, χ₁ + χ₂ ∈ s := by
      rintro - ⟨n₁, hn₁, rfl⟩ - ⟨n₂, hn₂, rfl⟩
      refine ⟨n₁ + n₂, by simp [hn₁], ?_⟩
      ext; simp [add_smul, Finset.sum_add_distrib]
    let e : {n : ι → ℕ | n ≠ 0} ≃ s :=
      .ofBijective (fun n ↦ ⟨∑ i, n.val i • b.baseSupp i, n.val, n.property, by ext; simp⟩) <| by
      refine ⟨fun n₁ n₂ h ↦ ?_, fun χ ↦ ?_⟩
      · ext i
        have := b.linearIndependent_baseSupp.restrict_scalars' ℕ
        refine Fintype.linearIndependent_iffₛ.mp this n₁ n₂ ?_ i
        ext v
        rw [Subtype.mk.injEq] at h
        simpa using congr_fun h v
      · use ⟨χ.property.choose, χ.property.choose_spec.1⟩
        ext i
        simpa using congr_fun χ.property.choose_spec.2.symm i
    replace hu : u ∈ ⨆ χ, ⨆ (_ : χ ∈ s), rootSpace H χ := by
      convert! hu; rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl
    replace hv : v ∈ ⨆ χ, ⨆ (_ : χ ∈ s), rootSpace H χ := by
      convert! hv; rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl
    convert! mem_biSup_genWeightSpace_of hs hu hv
    rw [iSup_subtype', iSup_subtype', ← e.iSup_comp]; rfl

/-- Lemma 4.4 from [Geck](Geck2017). -/
/-
**LieAlgebra.Basis.borelLower_le_biSup** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Bas
is`。
形式化陈述：borelLower_le_biSup : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `LieAlgebra.Basis.isLieAbelian_cartan`：isLieAbelian_cartan : IsLieAbelian
 H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LieAlgebra.rootSpace.congr_simp`：∀ {R : Type u_1} {L : Type u_2} [inst :
 CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   (H : LieSubalgebra
 R L) [inst_3 : LieRi…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieAlgebra.Basis.symm_baseSupp`：∀ {ι : Type u_1} {R : Type u_2} {L : Typ
e u_3} [inst : Finite ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : 
LieAlgebra R L] {H :…
· 使用引理 `LieAlgebra.Basis.borelUpper_le_biSup`：borelUpper_le_biSup : letI

--- 原说明 ---
Lemma 4.4 from [Geck](Geck2017).
-/
lemma borelLower_le_biSup :
    letI := b.isLieAbelian_cartan
    b.borelLower ≤ ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) := by
  simpa only [symm_baseSupp] using! b.symm.borelUpper_le_biSup
/-
**LieAlgebra.Basis.cartan_borelLower_borelUpper_le** 是 Mathlib 中的一个引理，位于命名空间 `Li
eAlgebra.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma cartan_borelLower_borelUpper_le :
    letI := b.isLieAbelian_cartan
    letI U := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • b.baseSupp i)
    ![H.toLieSubmodule, b.borelLower, b.borelUpper] ≤ ![rootSpace H 0, U, V] := by
  let := b.isLieAbelian_cartan
  intro i
  fin_cases i
  · exact toLieSubmodule_le_rootSpace_zero R L H
  · exact b.borelLower_le_biSup
  · exact b.borelUpper_le_biSup

variable [IsTorsionFree R L]

set_option backward.isDefEq.respectTransparency.types false in
/-
**LieAlgebra.Basis.iSupIndep_rootSpace** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Bas
is`。
形式化陈述：iSupIndep_rootSpace : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `LieAlgebra.Basis.isLieAbelian_cartan`：isLieAbelian_cartan : IsLieAbelian
 H
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
· 使用定理 `iSup_comm`：iSup_comm {f : ι -> ι' -> α} : ⨆ (i) (j), f i j = ⨆ (j) (i), 
f i j
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用引理 `LieAlgebra.Basis.linearIndependent_baseSupp`：linearIndependent_baseSupp 
[IsDomain R] [CharZero R] : LinearIndependent R b.baseSupp
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `LinearMap.coe_zero_iff`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {M : Type u_8}
 {M₂ : Type u_10} [inst : Semiring R₁] [inst_1 : Semiring R₂]   [inst_2 : AddCom
mMonoid M] […
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
（共 52 条，此处仅展示前 30 条）
-/
lemma iSupIndep_rootSpace :
    letI := b.isLieAbelian_cartan
    letI U := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • (-b.baseSupp) i)
    letI V := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • b.baseSupp i)
    iSupIndep ![rootSpace H 0, U, V] := by
  let := b.isLieAbelian_cartan
  set U := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) with hU
  set V := ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • b.baseSupp i) with hV
  set s0 : Set (H → R) := {0} with hs0
  set sU : Set (H → R) := {f | ∃ n : ι → ℕ, n ≠ 0 ∧ f = ∑ i, n i • (-b.baseSupp) i} with hsU
  set sV : Set (H → R) := {f | ∃ n : ι → ℕ, n ≠ 0 ∧ f = ∑ i, n i • b.baseSupp i} with hsV
  have hs0' : rootSpace H 0 = ⨆ i ∈ s0, LieModule.genWeightSpace L i := by simp [hs0]
  have hsU' : U = ⨆ i ∈ sU, LieModule.genWeightSpace L i := by
    simp only [hU, hsU, mem_ofPred_eq, iSup_exists, iSup_and, iSup_comm (ι := H → R),
      iSup_iSup_eq_left, LinearMap.coe_sum, LinearMap.coe_smul]
  have hsV' : V = ⨆ i ∈ sV, LieModule.genWeightSpace L i := by
    simp only [hV, hsV, mem_ofPred_eq, iSup_exists, iSup_and, iSup_comm (ι := H → R),
      iSup_iSup_eq_left, LinearMap.coe_sum, LinearMap.coe_smul]
  have hU0 : Disjoint s0 sU := by
    suffices ∀ g ∈ sU, g ≠ 0 by
      refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg ↦ ?_
      obtain ⟨rfl⟩ : f = 0 := by simpa [hs0] using hf
      exact (this _ hg).symm
    intro g hg contra
    obtain ⟨n, hn, rfl⟩ : ∃ n : ι → ℕ, n ≠ 0 ∧ g = -∑ i, n i • b.baseSupp i := by
      simpa [hsU] using hg
    rw [neg_eq_zero, LinearMap.coe_zero_iff] at contra
    have := Fintype.linearIndependent_iff.mp b.linearIndependent_baseSupp ((↑) ∘ n)
      (by simpa [Nat.cast_smul_eq_nsmul])
    exact hn <| funext fun i ↦ by simpa using this i
  have hV0 : Disjoint s0 sV := by
    suffices ∀ g ∈ sV, g ≠ 0 by
      refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg ↦ ?_
      obtain ⟨rfl⟩ : f = 0 := by simpa [hs0] using hf
      exact (this _ hg).symm
    intro g hg contra
    obtain ⟨n, hn, rfl⟩ : ∃ n : ι → ℕ, n ≠ 0 ∧ g = ∑ i, n i • b.baseSupp i := by
      simpa [hsV] using hg
    rw [LinearMap.coe_zero_iff] at contra
    have := Fintype.linearIndependent_iff.mp b.linearIndependent_baseSupp ((↑) ∘ n)
      (by simpa [Nat.cast_smul_eq_nsmul])
    exact hn <| funext fun i ↦ by simpa using this i
  have hUV : Disjoint sU sV := by
    refine Set.disjoint_iff_forall_ne.mpr fun f hf g hg ↦ ?_
    rintro rfl
    obtain ⟨n, hn, hn'⟩ : ∃ n : ι → ℕ, n ≠ 0 ∧ f = -∑ i, n i • b.baseSupp i := by
      simpa [hsU] using hf
    obtain ⟨m, hm, rfl⟩ : ∃ m : ι → ℕ, m ≠ 0 ∧ f = ∑ i, m i • b.baseSupp i := by
      simpa [hsV] using hg
    replace hn' : ∑ i, (((↑) : ℕ → R) ∘ (m + n)) i • b.baseSupp i = 0 := by
      rw [eq_neg_iff_add_eq_zero] at hn'
      change ⇑(∑ i, m i • b.baseSupp i + ∑ i, n i • b.baseSupp i) = 0 at hn'
      simp_rw [LinearMap.coe_zero_iff, ← Finset.sum_add_distrib, ← add_smul, ← Pi.add_apply,
        ← Nat.cast_smul_eq_nsmul R] at hn'
      exact hn'
    have := Fintype.linearIndependent_iff.mp b.linearIndependent_baseSupp ((↑) ∘ (m + n)) hn'
    refine hn <| funext fun i ↦ ?_
    specialize this i
    rw [comp_apply, Nat.cast_eq_zero, Pi.add_apply, Nat.add_eq_zero_iff] at this
    simpa using this.2
  have key := LieModule.iSupIndep_genWeightSpace R H L
  have h₀ : Disjoint (rootSpace H 0) (U ⊔ V) := by
    convert! key.disjoint_biSup_biSup (hU0.union_right hV0)
    rw [iSup_union, hsU', hsV']
  have h₁ : Disjoint U (V ⊔ rootSpace H 0) := by
    convert! key.disjoint_biSup_biSup (hUV.union_right hU0.symm)
    rw [iSup_union, hs0', hsV']
  have h₂ : Disjoint V (rootSpace H 0 ⊔ U) := by
    convert! key.disjoint_biSup_biSup (Disjoint.union_left hV0 hUV).symm
    rw [iSup_union, hs0', hsU']
  simp [iSupIndep_fin_three, h₀, h₁, h₂]

set_option linter.unusedFintypeInType false in
/-
**LieAlgebra.Basis.cartan_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：cartan_eq : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `LieAlgebra.Basis.isLieAbelian_cartan`：isLieAbelian_cartan : IsLieAbelian
 H
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `iSupIndep.le_iff_eq_of_iSup_eq_top`：iSupIndep.le_iff_eq_of_iSup_eq_top [
IsModularLattice α] {f g : ι -> α} (h₁ : iSupIndep g) (h₂ : iSup f = ⊤) : f <= g
 ↔ f = g
· 使用定理 `LieSubmodule.instIsModularLattice`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `LieAlgebra.Basis.iSupIndep_rootSpace`：iSupIndep_rootSpace : letI
· 使用引理 `LieAlgebra.Basis.iSup_cartan_borelLower_borelUpper_eq_top`：iSup_cartan_b
orelLower_borelUpper_eq_top : iSup ![H.toLieSubmodule, b.borelLower, b.borelUppe
r] = ⊤
· 使用定理 `_private.Mathlib.Algebra.Lie.Basis.Basic.0.LieAlgebra.Basis.cartan_borel
Lower_borelUpper_le`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [inst : Fini
te ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H 
:…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma cartan_eq :
    letI := b.isLieAbelian_cartan
    H.toLieSubmodule = rootSpace H 0 :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 0
/-
**LieAlgebra.Basis.borelLower_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：borelLower_eq : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `LieAlgebra.Basis.isLieAbelian_cartan`：isLieAbelian_cartan : IsLieAbelian
 H
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `iSupIndep.le_iff_eq_of_iSup_eq_top`：iSupIndep.le_iff_eq_of_iSup_eq_top [
IsModularLattice α] {f g : ι -> α} (h₁ : iSupIndep g) (h₂ : iSup f = ⊤) : f <= g
 ↔ f = g
· 使用定理 `LieSubmodule.instIsModularLattice`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `LieAlgebra.Basis.iSupIndep_rootSpace`：iSupIndep_rootSpace : letI
· 使用引理 `LieAlgebra.Basis.iSup_cartan_borelLower_borelUpper_eq_top`：iSup_cartan_b
orelLower_borelUpper_eq_top : iSup ![H.toLieSubmodule, b.borelLower, b.borelUppe
r] = ⊤
· 使用定理 `_private.Mathlib.Algebra.Lie.Basis.Basic.0.LieAlgebra.Basis.cartan_borel
Lower_borelUpper_le`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [inst : Fini
te ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H 
:…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma borelLower_eq :
    letI := b.isLieAbelian_cartan
    b.borelLower = ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • (-b.baseSupp) i) :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 1
/-
**LieAlgebra.Basis.borelUpper_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Basis`。
形式化陈述：borelUpper_eq : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `LieAlgebra.Basis.isLieAbelian_cartan`：isLieAbelian_cartan : IsLieAbelian
 H
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `iSupIndep.le_iff_eq_of_iSup_eq_top`：iSupIndep.le_iff_eq_of_iSup_eq_top [
IsModularLattice α] {f g : ι -> α} (h₁ : iSupIndep g) (h₂ : iSup f = ⊤) : f <= g
 ↔ f = g
· 使用定理 `LieSubmodule.instIsModularLattice`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `LieAlgebra.Basis.iSupIndep_rootSpace`：iSupIndep_rootSpace : letI
· 使用引理 `LieAlgebra.Basis.iSup_cartan_borelLower_borelUpper_eq_top`：iSup_cartan_b
orelLower_borelUpper_eq_top : iSup ![H.toLieSubmodule, b.borelLower, b.borelUppe
r] = ⊤
· 使用定理 `_private.Mathlib.Algebra.Lie.Basis.Basic.0.LieAlgebra.Basis.cartan_borel
Lower_borelUpper_le`：∀ {ι : Type u_1} {R : Type u_2} {L : Type u_3} [inst : Fini
te ι] [inst_1 : CommRing R] [inst_2 : LieRing L]   [inst_3 : LieAlgebra R L] {H 
:…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma borelUpper_eq :
    letI := b.isLieAbelian_cartan
    b.borelUpper = ⨆ (n : ι → ℕ) (_ : n ≠ 0), rootSpace H (∑ i, n i • b.baseSupp i) :=
  congr_fun ((b.iSupIndep_rootSpace.le_iff_eq_of_iSup_eq_top
    b.iSup_cartan_borelLower_borelUpper_eq_top).mp b.cartan_borelLower_borelUpper_le) 2

set_option linter.unusedFintypeInType false in
include b in
/-
**LieAlgebra.Basis.isCartanSubalgebra** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Basi
s`。
形式化陈述：isCartanSubalgebra [IsNoetherian R L] : H.IsCartanSubalgebra
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `LieAlgebra.Basis.isLieAbelian_cartan`：isLieAbelian_cartan : IsLieAbelian
 H
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.eq_rootSpace_zero_iff_isCartan`：eq_rootSpace_zero_iff_isCarta
n [IsNoetherian R L] : H.toLieSubmodule = rootSpace H 0 ↔ H.IsCartanSubalgebra
· 使用引理 `LieAlgebra.Basis.cartan_eq`：cartan_eq : letI
-/
lemma isCartanSubalgebra [IsNoetherian R L] : H.IsCartanSubalgebra := by
  let := b.isLieAbelian_cartan
  rw [← eq_rootSpace_zero_iff_isCartan, b.cartan_eq]

end CommRing

end Basis

end LieAlgebra

