/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.Data.Finsupp.Lex

/-!
# Well-foundedness of the lexicographic and product orders on `Finsupp`

`Finsupp.Lex.wellFounded` and the two variants that follow it essentially say that if `(· > ·)` is
a well order on `α`, `(· < ·)` is well-founded on `N`, and `0` is a bottom element in `N`, then the
lexicographic `(· < ·)` is well-founded on `α →₀ N`.

`Finsupp.Lex.wellFoundedLT_of_finite` says that if `α` is finite and equipped with a linear order
and `(· < ·)` is well-founded on `N`, then the lexicographic `(· < ·)` is well-founded on `α →₀ N`.

`Finsupp.wellFoundedLT` and `wellFoundedLT_of_finite` state the same results for the product
order `(· < ·)`, but without the ordering conditions on `α`.

All results are transferred from `DFinsupp` via `Finsupp.toDFinsupp`.
-/

public section


variable {α N : Type*}

namespace Finsupp

variable [Zero N] {r : α → α → Prop} {s : N → N → Prop}

/-- Transferred from `DFinsupp.Lex.acc`. See the top of that file for an explanation for the
  appearance of the relation `rᶜ ⊓ (≠)`. -/
/-
**Finsupp.Lex.acc** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] {r : α → α → Prop} {s : N 
→ N → Prop},   (∀ ⦃n : N⦄, ¬s n 0) →     WellFounded s → ∀ (x : α →₀ N), (∀ a ∈ 
x.support, Acc (rᶜ ⊓ fun x1 x2 => x1 ≠ x2) a) → Acc (Finsupp.Lex r s) x
参数：∀ ⦃n : N⦄, ¬s n 0；x : α →₀ N；∀ a ∈ x.support, Acc (rᶜ ⊓ fun x1 x2 => x1 ≠ x2)
 a；Finsupp.Lex r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.lex_eq_invImage_dfinsupp_lex`：lex_eq_invImage_dfinsupp_lex (r : 
α -> α -> Prop) (s : N -> N -> Prop) : Finsupp.Lex r s = InvImage (DFinsupp.Lex 
r fun _ => s) toDFinsupp
· 使用定理 `InvImage.accessible`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} {a :
 α} (f : α → β), Acc r (f a) → Acc (InvImage r f) a
· 使用定理 `DFinsupp.Lex.acc`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i : ι) → 
Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃i : ι⦄ ⦃a
 : α i…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toDFinsupp_support`：toDFinsupp_support (f : ι ->₀ M) : f.toDFinsupp.supp
ort = f.support

--- 原说明 ---
Transferred from `DFinsupp.Lex.acc`. See the top of that file for an explanation
 for the
  appearance of the relation `rᶜ ⊓ (≠)`.
-/
theorem Lex.acc (hbot : ∀ ⦃n⦄, ¬s n 0) (hs : WellFounded s) (x : α →₀ N)
    (h : ∀ a ∈ x.support, Acc (rᶜ ⊓ (· ≠ ·)) a) :
    Acc (Finsupp.Lex r s) x := by
  rw [lex_eq_invImage_dfinsupp_lex]
  classical
    refine InvImage.accessible toDFinsupp (DFinsupp.Lex.acc (fun _ => hbot) (fun _ => hs) _ ?_)
    simpa only [toDFinsupp_support] using h
/-
**Finsupp.Lex.wellFounded** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] {r : α → α → Prop} {s : N 
→ N → Prop},   (∀ ⦃n : N⦄, ¬s n 0) → WellFounded s → WellFounded (rᶜ ⊓ fun x1 x2
 => x1 ≠ x2) → WellFounded (Finsupp.Lex r s)
参数：∀ ⦃n : N⦄, ¬s n 0；rᶜ ⊓ fun x1 x2 => x1 ≠ x2；Finsupp.Lex r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.acc`：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] {r : α 
→ α → Prop} {s : N → N → Prop},   (∀ ⦃n : N⦄, ¬s n 0) →     WellFounded s → ∀ (x
 : α …
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a
-/
theorem Lex.wellFounded (hbot : ∀ ⦃n⦄, ¬s n 0) (hs : WellFounded s)
    (hr : WellFounded <| rᶜ ⊓ (· ≠ ·)) : WellFounded (Finsupp.Lex r s) :=
  ⟨fun x => Lex.acc hbot hs x fun a _ => hr.apply a⟩
/-
**Finsupp.Lex.wellFounded'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] {r : α → α → Prop} {s : N 
→ N → Prop},   (∀ ⦃n : N⦄, ¬s n 0) →     WellFounded s → ∀ [Std.Trichotomous r],
 WellFounded (Function.swap r) → WellFounded (Finsupp.Lex r s)
参数：∀ ⦃n : N⦄, ¬s n 0；Function.swap r；Finsupp.Lex r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `DFinsupp.Lex.wellFounded'`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (
i : ι) → Zero (α i)] {r : ι → ι → Prop} {s : (i : ι) → α i → α i → Prop},   (∀ ⦃
i : ι⦄ ⦃a : α i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.lex_eq_invImage_dfinsupp_lex`：lex_eq_invImage_dfinsupp_lex (r : 
α -> α -> Prop) (s : N -> N -> Prop) : Finsupp.Lex r s = InvImage (DFinsupp.Lex 
r fun _ => s) toDFinsupp
-/
theorem Lex.wellFounded' (hbot : ∀ ⦃n⦄, ¬s n 0) (hs : WellFounded s)
    [Std.Trichotomous r] (hr : WellFounded (Function.swap r)) : WellFounded (Finsupp.Lex r s) :=
  (lex_eq_invImage_dfinsupp_lex r s).symm ▸
    InvImage.wf _ (DFinsupp.Lex.wellFounded' (fun _ => hbot) (fun _ => hs) hr)
/-
**Finsupp.Lex.wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_3} {N : Type u_4} [inst : LT α] [Std.Trichotomous fun x1 x2 
=> x1 < x2] [hα : WellFoundedGT α]   [inst_2 : AddMonoid N] [inst_3 : PartialOrd
er N] [IsBotZeroClass N] [hN : WellFoundedLT N],   WellFoundedLT (Lex (α →₀ N))
参数：Lex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.wellFounded'`：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N
] {r : α → α → Prop} {s : N → N → Prop},   (∀ ⦃n : N⦄, ¬s n 0) →     WellFounded
 s → ∀ [Std.Tr…
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
instance Lex.wellFoundedLT {α N} [LT α] [@Std.Trichotomous α (· < ·)] [hα : WellFoundedGT α]
    [AddMonoid N] [PartialOrder N] [IsBotZeroClass N]
    [hN : WellFoundedLT N] : WellFoundedLT (Lex (α →₀ N)) :=
  ⟨Lex.wellFounded' (fun _ => not_lt_zero) hN.wf hα.wf⟩
/-
**Finsupp.Colex.wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex`。
形式化陈述：∀ {α : Type u_3} {N : Type u_4} [inst : LT α] [Std.Trichotomous fun x1 x2 
=> x1 < x2] [WellFoundedLT α]   [inst_3 : AddMonoid N] [inst_4 : PartialOrder N]
 [IsBotZeroClass N] [WellFoundedLT N], WellFoundedLT (Colex (α →₀ N))
参数：Colex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.wellFoundedLT`：∀ {α : Type u_3} {N : Type u_4} [inst : LT α]
 [Std.Trichotomous fun x1 x2 => x1 < x2] [hα : WellFoundedGT α]   [inst_2 : AddM
onoid N] [inst_…
· 使用定理 `OrderDual.instTrichotomousLt`：∀ {α : Type u_1} [inst : LT α] [T : Std.Tr
ichotomous LT.lt], Std.Trichotomous LT.lt
· 使用定理 `instWellFoundedGTOrderDualOfWellFoundedLT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedLT α], WellFoundedGT αᵒᵈ
-/
instance Colex.wellFoundedLT {α N} [LT α] [@Std.Trichotomous α (· < ·)] [WellFoundedLT α]
    [AddMonoid N] [PartialOrder N] [IsBotZeroClass N]
    [WellFoundedLT N] : WellFoundedLT (Colex (α →₀ N)) :=
  Lex.wellFoundedLT (α := αᵒᵈ)

variable (r)
/-
**Finsupp.Lex.wellFounded_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] (r : α → α → Prop) {s : N 
→ N → Prop} [IsStrictTotalOrder α r]   [Finite α], WellFounded s → WellFounded (
Finsupp.Lex r s)
参数：r : α → α → Prop；Finsupp.Lex r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `Pi.Lex.wellFounded`：Pi.Lex.wellFounded [IsStrictTotalOrder ι r] [Finite 
ι] (hs : forall i, WellFounded (s i)) : WellFounded (Pi.Lex r (fun {i} => s i))
-/
theorem Lex.wellFounded_of_finite [IsStrictTotalOrder α r] [Finite α]
    (hs : WellFounded s) : WellFounded (Finsupp.Lex r s) :=
  InvImage.wf (@equivFunOnFinite α N _ _) (Pi.Lex.wellFounded r fun _ => hs)
/-
**Finsupp.Lex.wellFoundedLT_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lex`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : LinearOrder α] [
Finite α] [inst_3 : LT N]   [hwf : WellFoundedLT N], WellFoundedLT (Lex (α →₀ N)
)
参数：Lex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.wellFounded_of_finite`：∀ {α : Type u_1} {N : Type u_2} [inst
 : Zero N] (r : α → α → Prop) {s : N → N → Prop} [IsStrictTotalOrder α r]   [Fin
ite α], WellFounded s →…
· 使用定理 `instIsStrictTotalOrderLt`：∀ {α : Type u} [inst : LinearOrder α], IsStric
tTotalOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
theorem Lex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
    [hwf : WellFoundedLT N] : WellFoundedLT (Lex (α →₀ N)) :=
  ⟨Finsupp.Lex.wellFounded_of_finite (· < ·) hwf.1⟩
/-
**Finsupp.Colex.wellFoundedLT_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Colex
`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : LinearOrder α] [
Finite α] [inst_3 : LT N] [WellFoundedLT N],   WellFoundedLT (Colex (α →₀ N))
参数：Colex (α →₀ N)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.Lex.wellFoundedLT_of_finite`：∀ {α : Type u_1} {N : Type u_2} [in
st : Zero N] [inst_1 : LinearOrder α] [Finite α] [inst_3 : LT N]   [hwf : WellFo
undedLT N], WellFoundedLT…
-/
theorem Colex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
    [WellFoundedLT N] : WellFoundedLT (Colex (α →₀ N)) :=
  Lex.wellFoundedLT_of_finite (α := αᵒᵈ)
/-
**Finsupp.wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [inst_1 : Preorder N] [Wel
lFoundedLT N],   (∀ (n : N), ¬n < 0) → WellFoundedLT (α →₀ N)
参数：∀ (n : N), ¬n < 0；α →₀ N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `DFinsupp.wellFoundedLT`：∀ {ι : Type u_1} {α : ι → Type u_2} [inst : (i :
 ι) → Zero (α i)] [inst_1 : (i : ι) → Preorder (α i)]   [∀ (i : ι), WellFoundedL
T (α i)], (∀…
-/
protected theorem wellFoundedLT [Preorder N] [WellFoundedLT N] (hbot : ∀ n : N, ¬n < 0) :
    WellFoundedLT (α →₀ N) :=
  ⟨InvImage.wf toDFinsupp (DFinsupp.wellFoundedLT fun _ a => hbot a).wf⟩
/-
**Finsupp.wellFoundedLT'** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：wellFoundedLT' {N} [AddMonoid N] [PartialOrder N] [IsBotZeroClass N] [Well
FoundedLT N] : WellFoundedLT (α ->₀ N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.wellFoundedLT`：∀ {α : Type u_1} {N : Type u_2} [inst : Zero N] [
inst_1 : Preorder N] [WellFoundedLT N],   (∀ (n : N), ¬n < 0) → WellFoundedLT (α
 →₀ N)
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
-/
instance wellFoundedLT' {N}
    [AddMonoid N] [PartialOrder N] [IsBotZeroClass N] [WellFoundedLT N] :
    WellFoundedLT (α →₀ N) :=
  Finsupp.wellFoundedLT fun _ => not_lt_zero
/-
**Finsupp.wellFoundedLT_of_finite** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：wellFoundedLT_of_finite [Finite α] [Preorder N] [WellFoundedLT N] : WellFo
undedLT (α ->₀ N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `InvImage.wf`：∀ {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β),
 WellFounded r → WellFounded (InvImage r f)
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
instance wellFoundedLT_of_finite [Finite α] [Preorder N] [WellFoundedLT N] :
    WellFoundedLT (α →₀ N) :=
  ⟨InvImage.wf equivFunOnFinite Function.wellFoundedLT.wf⟩

end Finsupp

