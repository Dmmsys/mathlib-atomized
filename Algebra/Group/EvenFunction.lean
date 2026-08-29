/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Module.Defs

/-!
# Even and odd functions

We define even functions `α → β` assuming `α` has a negation, and odd functions assuming both `α`
and `β` have negation.

These definitions are `Function.Even` and `Function.Odd`; and they are `protected`, to avoid
conflicting with the root-level definitions `Even` and `Odd` (which, for functions, mean that the
function takes even resp. odd _values_, a wholly different concept).
-/

@[expose] public section

assert_not_exists Module.IsTorsionFree NoZeroSMulDivisors

namespace Function

variable {α β : Type*} [Neg α]

/--
Definition of `Even` / `Even` 的定义

English:
definition Even
  signature: (f : α -> β)
  body: forall a, f (-a) = f a

中文:
定义 Even
  签名: (f : α -> β)
  定义体: forall a, f (-a) = f a
-/
protected def Even (f : α -> β) : Prop := forall a, f (-a) = f a

/--
Definition of `Odd` / `Odd` 的定义

English:
definition Odd
  signature: [Neg β] (f : α -> β)
  body: forall a, f (-a) = -(f a)

中文:
定义 Odd
  签名: [取负 β] (f : α -> β)
  定义体: forall a, f (-a) = -(f a)
-/
protected def Odd [Neg β] (f : α -> β) : Prop := forall a, f (-a) = -(f a)

/--
lemma `Even.eq` / 引理 `Even.eq`

English:
lemma Even.eq
  given: {f : α -> β} (hf : f.Even) (x : α)
  statement: f (-x) = f x
  proof: hf x

中文:
引理 Even.eq
  条件: {f : α -> β} (hf : f.Even) (x : α)
  结论: f (-x) = f x
  证明: hf x
-/
lemma Even.eq {f : α -> β} (hf : f.Even) (x : α) : f (-x) = f x := hf x

/--
lemma `Even.const` / 引理 `Even.const`

English:
lemma Even.const
  given: (b : β)
  statement: Function.Even (fun _ : α => b)
  proof: fun _ => rfl

中文:
引理 Even.const
  条件: (b : β)
  结论: 函数.Even (fun _ : α => b)
  证明: fun _ => rfl
-/
lemma Even.const (b : β) : Function.Even (fun _ : α => b) := fun _ => rfl

/--
lemma `Even.zero` / 引理 `Even.zero`

English:
lemma Even.zero
  given: [Zero β]
  statement: Function.Even (fun (_ : α) => (0 : β))
  proof: Even.const 0

中文:
引理 Even.zero
  条件: [零 β]
  结论: 函数.Even (fun (_ : α) => (0 : β))
  证明: Even.const 0

Depends on / 依赖: Even.const
-/
lemma Even.zero [Zero β] : Function.Even (fun (_ : α) => (0 : β)) := Even.const 0

/--
lemma `Odd.eq` / 引理 `Odd.eq`

English:
lemma Odd.eq
  given: [Neg β] {f : α -> β} (hf : f.Odd) (x : α)
  statement: f (-x) = -f x
  proof: hf x

中文:
引理 Odd.eq
  条件: [取负 β] {f : α -> β} (hf : f.Odd) (x : α)
  结论: f (-x) = -f x
  证明: hf x
-/
lemma Odd.eq [Neg β] {f : α -> β} (hf : f.Odd) (x : α) : f (-x) = -f x := hf x

/--
lemma `Odd.zero` / 引理 `Odd.zero`

English:
lemma Odd.zero
  given: [NegZeroClass β]
  statement: Function.Odd (fun (_ : α) => (0 : β))
  proof: fun _ => neg_zero.symm

中文:
引理 Odd.zero
  条件: [NegZero类 β]
  结论: 函数.Odd (fun (_ : α) => (0 : β))
  证明: fun _ => neg_zero.symm

Depends on / 依赖: neg_zero, neg_zero.symm
-/
lemma Odd.zero [NegZeroClass β] : Function.Odd (fun (_ : α) => (0 : β)) := fun _ => neg_zero.symm

section composition

variable {γ : Type*}

/--
lemma `Even.left_comp` / 引理 `Even.left_comp`

English:
lemma Even.left_comp
  given: {g : α -> β} (hg : g.Even) (f : β -> γ)
  statement: (f ∘ g).Even
  proof: (congr_arg f <| hg ·)

中文:
引理 Even.left_comp
  条件: {g : α -> β} (hg : g.Even) (f : β -> γ)
  结论: (f ∘ g).Even
  证明: (congr_arg f <| hg ·)

Depends on / 依赖: congr_arg
-/
lemma Even.left_comp {g : α -> β} (hg : g.Even) (f : β -> γ) : (f ∘ g).Even :=
  (congr_arg f <| hg ·)

/--
lemma `Even.comp_odd` / 引理 `Even.comp_odd`

English:
lemma Even.comp_odd
  given: [Neg β] {f : β -> γ} (hf : f.Even) {g : α -> β} (hg : g.Odd)
  proof: by
  intro a
  simp only [comp_apply, hg a, hf _]

中文:
引理 Even.comp_odd
  条件: [取负 β] {f : β -> γ} (hf : f.Even) {g : α -> β} (hg : g.Odd)
  证明: by
  intro a
  simp only [comp_apply, hg a, hf _]

Depends on / 依赖: comp_apply
-/
lemma Even.comp_odd [Neg β] {f : β -> γ} (hf : f.Even) {g : α -> β} (hg : g.Odd) :
    (f ∘ g).Even := by
  intro a
  simp only [comp_apply, hg a, hf _]

/--
lemma `Odd.comp_odd` / 引理 `Odd.comp_odd`

English:
lemma Odd.comp_odd
  given: [Neg β] [Neg γ] {f : β -> γ} (hf : f.Odd) {g : α -> β} (hg : g.Odd)
  proof: by
  intro a
  simp only [comp_apply, hg a, hf _]

中文:
引理 Odd.comp_odd
  条件: [取负 β] [取负 γ] {f : β -> γ} (hf : f.Odd) {g : α -> β} (hg : g.Odd)
  证明: by
  intro a
  simp only [comp_apply, hg a, hf _]

Depends on / 依赖: comp_apply
-/
lemma Odd.comp_odd [Neg β] [Neg γ] {f : β -> γ} (hf : f.Odd) {g : α -> β} (hg : g.Odd) :
    (f ∘ g).Odd := by
  intro a
  simp only [comp_apply, hg a, hf _]

end composition

/--
lemma `Even.add` / 引理 `Even.add`

English:
lemma Even.add
  given: [Add β] {f g : α -> β} (hf : f.Even) (hg : g.Even)
  statement: (f + g).Even
  proof: by
  intro a
  simp only [hf a, hg a, Pi.add_apply]

中文:
引理 Even.add
  条件: [加法 β] {f g : α -> β} (hf : f.Even) (hg : g.Even)
  结论: (f + g).Even
  证明: by
  intro a
  simp only [hf a, hg a, Pi.add_apply]

Depends on / 依赖: Pi.add_apply, add_apply
-/
lemma Even.add [Add β] {f g : α -> β} (hf : f.Even) (hg : g.Even) : (f + g).Even := by
  intro a
  simp only [hf a, hg a, Pi.add_apply]

/--
lemma `Odd.add` / 引理 `Odd.add`

English:
lemma Odd.add
  given: [SubtractionCommMonoid β] {f g : α -> β} (hf : f.Odd) (hg : g.Odd)
  statement: (f + g).Odd
  proof: by
  intro a
  simp only [hf a, hg a, Pi.add_apply, neg_add]

中文:
引理 Odd.add
  条件: [SubtractionComm幺半群 β] {f g : α -> β} (hf : f.Odd) (hg : g.Odd)
  结论: (f + g).Odd
  证明: by
  intro a
  simp only [hf a, hg a, Pi.add_apply, neg_add]

Depends on / 依赖: Pi.add_apply, add_apply, neg_add
-/
lemma Odd.add [SubtractionCommMonoid β] {f g : α -> β} (hf : f.Odd) (hg : g.Odd) : (f + g).Odd := by
  intro a
  simp only [hf a, hg a, Pi.add_apply, neg_add]

section smul

variable {γ : Type*} {f : α -> β} {g : α -> γ}

/--
lemma `Even.smul_even` / 引理 `Even.smul_even`

English:
lemma Even.smul_even
  given: [SMul β γ] (hf : f.Even) (hg : g.Even)
  statement: (f • g).Even
  proof: by
  intro a
  simp only [Pi.smul_apply', hf a, hg a]

中文:
引理 Even.smul_even
  条件: [标量乘法 β γ] (hf : f.Even) (hg : g.Even)
  结论: (f • g).Even
  证明: by
  intro a
  simp only [Pi.smul_apply', hf a, hg a]

Depends on / 依赖: Pi.smul_apply, smul_apply
-/
lemma Even.smul_even [SMul β γ] (hf : f.Even) (hg : g.Even) : (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a]

/--
lemma `Even.smul_odd` / 引理 `Even.smul_odd`

English:
lemma Even.smul_odd
  given: [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hf : f.Even) (hg : g.Odd)
  proof: by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg]

中文:
引理 Even.smul_odd
  条件: [幺半群 β] [加法群 γ] [分配乘法作用 β γ] (hf : f.Even) (hg : g.Odd)
  证明: by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg]

Depends on / 依赖: Pi.smul_apply, smul_apply, smul_neg
-/
lemma Even.smul_odd [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hf : f.Even) (hg : g.Odd) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg]

/--
lemma `Odd.smul_even` / 引理 `Odd.smul_even`

English:
lemma Odd.smul_even
  given: [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Even)
  proof: by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, neg_smul]

中文:
引理 Odd.smul_even
  条件: [环 β] [加法交换群 γ] [模 β γ] (hf : f.Odd) (hg : g.Even)
  证明: by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, neg_smul]

Depends on / 依赖: Pi.smul_apply, neg_smul, smul_apply
-/
lemma Odd.smul_even [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Even) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, neg_smul]

/--
lemma `Odd.smul_odd` / 引理 `Odd.smul_odd`

English:
lemma Odd.smul_odd
  given: [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Odd)
  proof: by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg, neg_smul, neg_neg]

中文:
引理 Odd.smul_odd
  条件: [环 β] [加法交换群 γ] [模 β γ] (hf : f.Odd) (hg : g.Odd)
  证明: by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg, neg_smul, neg_neg]

Depends on / 依赖: Pi.smul_apply, neg_neg, neg_smul, smul_apply, smul_neg
-/
lemma Odd.smul_odd [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Odd) :
    (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg, neg_smul, neg_neg]

/--
lemma `Even.const_smul` / 引理 `Even.const_smul`

English:
lemma Even.const_smul
  given: [SMul β γ] (hg : g.Even) (r : β)
  statement: (r • g).Even
  proof: by
  intro a
  simp only [Pi.smul_apply, hg a]

中文:
引理 Even.const_smul
  条件: [标量乘法 β γ] (hg : g.Even) (r : β)
  结论: (r • g).Even
  证明: by
  intro a
  simp only [Pi.smul_apply, hg a]

Depends on / 依赖: Pi.smul_apply, smul_apply
-/
lemma Even.const_smul [SMul β γ] (hg : g.Even) (r : β) : (r • g).Even := by
  intro a
  simp only [Pi.smul_apply, hg a]

/--
lemma `Odd.const_smul` / 引理 `Odd.const_smul`

English:
lemma Odd.const_smul
  given: [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hg : g.Odd) (r : β)
  proof: by
  intro a
  simp only [Pi.smul_apply, hg a, smul_neg]

中文:
引理 Odd.const_smul
  条件: [幺半群 β] [加法群 γ] [分配乘法作用 β γ] (hg : g.Odd) (r : β)
  证明: by
  intro a
  simp only [Pi.smul_apply, hg a, smul_neg]

Depends on / 依赖: Pi.smul_apply, smul_apply, smul_neg
-/
lemma Odd.const_smul [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hg : g.Odd) (r : β) :
    (r • g).Odd := by
  intro a
  simp only [Pi.smul_apply, hg a, smul_neg]

end smul

section mul

variable {R : Type*} [Mul R] {f g : α -> R}

/--
lemma `Even.mul_even` / 引理 `Even.mul_even`

English:
lemma Even.mul_even
  given: (hf : f.Even) (hg : g.Even)
  statement: (f * g).Even
  proof: by
  intro a
  simp only [Pi.mul_apply, hf a, hg a]

中文:
引理 Even.mul_even
  条件: (hf : f.Even) (hg : g.Even)
  结论: (f * g).Even
  证明: by
  intro a
  simp only [Pi.mul_apply, hf a, hg a]

Depends on / 依赖: Pi.mul_apply, mul_apply
-/
lemma Even.mul_even (hf : f.Even) (hg : g.Even) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a]

/--
lemma `Even.mul_odd` / 引理 `Even.mul_odd`

English:
lemma Even.mul_odd
  given: [HasDistribNeg R] (hf : f.Even) (hg : g.Odd)
  statement: (f * g).Odd
  proof: by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg]

中文:
引理 Even.mul_odd
  条件: [有DistribNeg R] (hf : f.Even) (hg : g.Odd)
  结论: (f * g).Odd
  证明: by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg]

Depends on / 依赖: Pi.mul_apply, mul_apply, mul_neg
-/
lemma Even.mul_odd [HasDistribNeg R] (hf : f.Even) (hg : g.Odd) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg]

/--
lemma `Odd.mul_even` / 引理 `Odd.mul_even`

English:
lemma Odd.mul_even
  given: [HasDistribNeg R] (hf : f.Odd) (hg : g.Even)
  statement: (f * g).Odd
  proof: by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, neg_mul]

中文:
引理 Odd.mul_even
  条件: [有DistribNeg R] (hf : f.Odd) (hg : g.Even)
  结论: (f * g).Odd
  证明: by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, neg_mul]

Depends on / 依赖: Pi.mul_apply, mul_apply, neg_mul
-/
lemma Odd.mul_even [HasDistribNeg R] (hf : f.Odd) (hg : g.Even) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, neg_mul]

/--
lemma `Odd.mul_odd` / 引理 `Odd.mul_odd`

English:
lemma Odd.mul_odd
  given: [HasDistribNeg R] (hf : f.Odd) (hg : g.Odd)
  statement: (f * g).Even
  proof: by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg, neg_mul, neg_neg]

中文:
引理 Odd.mul_odd
  条件: [有DistribNeg R] (hf : f.Odd) (hg : g.Odd)
  结论: (f * g).Even
  证明: by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg, neg_mul, neg_neg]

Depends on / 依赖: Pi.mul_apply, mul_apply, mul_neg, neg_mul, neg_neg
-/
lemma Odd.mul_odd [HasDistribNeg R] (hf : f.Odd) (hg : g.Odd) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg, neg_mul, neg_neg]

end mul

section torsionfree

-- need to redeclare variables since `InvolutiveNeg α` conflicts with `Neg α`
variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α -> β}

/--
lemma `zero_of_even_and_odd` / 引理 `zero_of_even_and_odd`

English:
lemma zero_of_even_and_odd
  given: [Neg α] (he : f.Even) (ho : f.Odd)
  statement: f = 0
  proof: by
  ext r
  rw [Pi.zero_apply]; rw [← neg_eq_self]; rw [← ho]; rw [he]

中文:
引理 zero_of_even_and_odd
  条件: [取负 α] (he : f.Even) (ho : f.Odd)
  结论: f = 0
  证明: by
  ext r
  rw [Pi.zero_apply]; rw [← neg_eq_self]; rw [← ho]; rw [he]

Depends on / 依赖: Pi.zero_apply, neg_eq_self, zero_apply
-/
lemma zero_of_even_and_odd [Neg α] (he : f.Even) (ho : f.Odd) : f = 0 := by
  ext r
  rw [Pi.zero_apply]; rw [← neg_eq_self]; rw [← ho]; rw [he]

/--
lemma `Odd.finsetSum_eq_zero` / 引理 `Odd.finsetSum_eq_zero`

English:
lemma Odd.finsetSum_eq_zero
  statement: [InvolutiveNeg α] {f : α -> β} (hf : f.Odd) {s : Finset α}
  proof: by
  simpa [neg_eq_self, funext hf, hs] using (Finset.sum_map s (Equiv.neg α).toEmbedding f).symm

@[deprecated (since := "2026-04-08")] alias Odd.finset_sum_eq_zero := Odd.finsetSum_eq_zero

中文:
引理 Odd.finsetSum_eq_zero
  结论: [InvolutiveNeg α] {f : α -> β} (hf : f.Odd) {s : 有限集 α}
  证明: by
  simpa [neg_eq_self, funext hf, hs] using (Finset.sum_map s (Equiv.neg α).toEmbedding f).symm

@[deprecated (since := "2026-04-08")] alias Odd.finset_sum_eq_zero := Odd.finsetSum_eq_zero

Depends on / 依赖: Equiv.neg, Finset, Finset.sum_map, neg_eq_self, sum_map, toEmbedding
-/
lemma Odd.finsetSum_eq_zero [InvolutiveNeg α] {f : α -> β} (hf : f.Odd) {s : Finset α}
    (hs : Finset.map (Equiv.neg α).toEmbedding s = s) :
    s.sum f = 0 := by
  simpa [neg_eq_self, funext hf, hs] using (Finset.sum_map s (Equiv.neg α).toEmbedding f).symm

@[deprecated (since := "2026-04-08")] alias Odd.finset_sum_eq_zero := Odd.finsetSum_eq_zero

/--
lemma `Odd.sum_eq_zero` / 引理 `Odd.sum_eq_zero`

English:
lemma Odd.sum_eq_zero
  given: [Fintype α] [InvolutiveNeg α] {f : α -> β} (hf : f.Odd)
  statement: ∑ a, f a = 0
  proof: hf.finsetSum_eq_zero Finset.map_univ_equiv (Equiv.neg α)

中文:
引理 Odd.sum_eq_zero
  条件: [有限类型 α] [InvolutiveNeg α] {f : α -> β} (hf : f.Odd)
  结论: ∑ a, f a = 0
  证明: hf.finsetSum_eq_zero Finset.map_univ_equiv (Equiv.neg α)

Depends on / 依赖: Equiv.neg, Finset, Finset.map_univ_equiv, finsetSum_eq_zero, hf.finsetSum_eq_zero, map_univ_equiv
-/
lemma Odd.sum_eq_zero [Fintype α] [InvolutiveNeg α] {f : α -> β} (hf : f.Odd) : ∑ a, f a = 0 :=
hf.finsetSum_eq_zero Finset.map_univ_equiv (Equiv.neg α)

/--
lemma `Odd.map_zero` / 引理 `Odd.map_zero`

English:
lemma Odd.map_zero
  given: [NegZeroClass α] (hf : f.Odd)
  statement: f 0 = 0
  proof: by simp [← neg_eq_self, ← hf 0]

中文:
引理 Odd.map_zero
  条件: [NegZero类 α] (hf : f.Odd)
  结论: f 0 = 0
  证明: by simp [← neg_eq_self, ← hf 0]

Depends on / 依赖: neg_eq_self
-/
lemma Odd.map_zero [NegZeroClass α] (hf : f.Odd) : f 0 = 0 := by simp [← neg_eq_self, ← hf 0]

end torsionfree

end Function
